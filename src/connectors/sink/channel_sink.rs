// Copyright 2021, The Tremor Team
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Sink implementation that keeps track of multiple streams and keeps channels to send to each stream

use crate::connectors::sink::{
    AsyncSinkReply, EventCfData, EventSerializer, SinkReply, StreamWriter,
};
use crate::connectors::{ConnectorContext, StreamDone};
use crate::errors::Result;
use crate::QSIZE;
use async_std::channel::{bounded, Receiver, Sender};
use async_std::task;
use beef::Cow;
use bimap::BiMap;
use either::Either;
use hashbrown::HashMap;
use std::hash::Hash;
use std::sync::atomic::Ordering;
use tremor_common::time::nanotime;
use tremor_pipeline::{CbAction, Event, SignalKind};
use tremor_value::Value;
use value_trait::ValueAccess;

use super::{ResultVec, Sink, SinkContext};

/// messages a channel sink can receive
pub enum ChannelSinkMsg<T>
where
    T: Hash + Eq + Send + 'static,
{
    /// add a new stream
    NewStream {
        /// the id of the stream
        stream_id: u64,
        /// stream metadata used for resolving a stream
        meta: Option<T>,
        /// sender to the actual stream handling data
        sender: Sender<SinkData>,
    },
    /// remove the stream
    RemoveStream(u64),
}

/// some data for a `ChannelSink` stream
#[derive(Clone, Debug)]
pub struct SinkData {
    /// data to send
    pub data: Vec<Vec<u8>>,
    /// async reply utils (if required)
    pub contraflow: Option<(EventCfData, Sender<AsyncSinkReply>)>,
    /// timestamp of processing start
    pub start: u64,
}

/// tracking 1 channel per stream
pub struct ChannelSink<T, F>
where
    T: Hash + Eq + Send + 'static,
    F: Fn(&Value<'_>) -> Option<T>,
{
    streams_meta: BiMap<T, u64>,
    streams: HashMap<u64, Sender<SinkData>>,
    resolver: F,
    tx: Sender<ChannelSinkMsg<T>>,
    rx: Receiver<ChannelSinkMsg<T>>,
    reply_tx: Sender<AsyncSinkReply>,
}

// FIXME: implement PauseBehaviour correctly
impl<T, F> ChannelSink<T, F>
where
    T: Hash + Eq + Send + 'static,
    F: Fn(&Value<'_>) -> Option<T>,
{
    /// constructor
    pub fn new(qsize: usize, resolver: F, reply_tx: Sender<AsyncSinkReply>) -> Self {
        let (tx, rx) = bounded(qsize);
        let streams = HashMap::with_capacity(8);
        let streams_meta = BiMap::with_capacity(8);
        Self {
            streams_meta,
            streams,
            resolver,
            tx,
            rx,
            reply_tx,
        }
    }

    /// hand out a `ChannelSinkRuntime` instance in order to register stream writers
    pub fn runtime(&self) -> ChannelSinkRuntime<T> {
        ChannelSinkRuntime {
            tx: self.tx.clone(),
        }
    }

    fn handle_channels_quickly(&mut self, serializer: &mut EventSerializer) -> bool {
        self.handle_channels(serializer, false)
    }
    /// returns true, if there are no more channels to send stuff to
    fn handle_channels(
        &mut self,
        serializer: &mut EventSerializer,
        clean_closed_streams: bool,
    ) -> bool {
        while let Ok(msg) = self.rx.try_recv() {
            match msg {
                ChannelSinkMsg::NewStream {
                    stream_id,
                    meta,
                    sender,
                } => {
                    trace!("[Sink::XXX] started new stream {}", stream_id);
                    self.streams.insert(stream_id, sender);
                    if let Some(meta) = meta {
                        self.streams_meta.insert(meta, stream_id);
                    }
                }
                ChannelSinkMsg::RemoveStream(stream_id) => {
                    self.remove_stream(stream_id);
                    serializer.drop_stream(stream_id);
                }
            }
        }
        // clean out closed streams
        if clean_closed_streams {
            for (stream_id, _) in self.streams.drain_filter(|_k, v| v.is_closed()) {
                self.streams_meta.remove_by_right(&stream_id);
                serializer.drop_stream(stream_id);
            }
        }
        self.streams.is_empty()
    }

    fn remove_stream(&mut self, stream_id: u64) {
        self.streams.remove(&stream_id);
        self.streams_meta.remove_by_right(&stream_id);
    }

    fn resolve_stream_from_meta<'lt, 'value>(
        &self,
        meta: &'lt Value<'value>,
        ctx: &SinkContext,
    ) -> Option<(&u64, &Sender<SinkData>)> {
        get_sink_meta(meta, ctx)
            .and_then(|sink_meta| (self.resolver)(sink_meta))
            .and_then(|stream_meta| self.streams_meta.get_by_left(&stream_meta))
            .and_then(|stream_id| {
                self.streams
                    .get(stream_id)
                    .map(|sender| (stream_id, sender))
            })
    }
}

#[derive(Clone)]
pub struct ChannelSinkRuntime<T>
where
    T: Hash + Eq + Send + 'static,
{
    tx: Sender<ChannelSinkMsg<T>>,
}

impl<T> ChannelSinkRuntime<T>
where
    T: Hash + Eq + Send + 'static,
{
    pub(crate) fn register_stream_writer<W>(
        &self,
        stream: u64,
        connection_meta: Option<T>,
        ctx: &ConnectorContext,
        mut writer: W,
    ) where
        W: StreamWriter + 'static,
    {
        let (stream_tx, stream_rx) = bounded::<SinkData>(QSIZE.load(Ordering::Relaxed));
        let stream_sink_tx = self.tx.clone();
        let ctx = ctx.clone();
        let tx = self.tx.clone();
        task::spawn(async move {
            tx.send(ChannelSinkMsg::NewStream {
                stream_id: stream,
                meta: connection_meta,
                sender: stream_tx,
            })
            .await?;
            // receive loop from channel sink
            while let (
                true,
                Ok(SinkData {
                    data,
                    contraflow,
                    start,
                }),
            ) = (
                ctx.quiescence_beacon.continue_writing().await,
                stream_rx.recv().await,
            ) {
                let failed = writer.write(data).await.is_err();

                // send asyn contraflow insights if requested (only if event.transactional)
                if let Some((cf_data, sender)) = contraflow {
                    let reply = if failed {
                        AsyncSinkReply::Fail(cf_data)
                    } else {
                        AsyncSinkReply::Ack(cf_data, nanotime() - start)
                    };
                    if let Err(e) = sender.send(reply).await {
                        error!(
                            "[Connector::{}] Error sending async sink reply: {}",
                            ctx.url, e
                        );
                    }
                }
                if failed {
                    break;
                }
            }
            let error = match writer.on_done(stream) {
                Err(e) => Some(e),
                Ok(StreamDone::ConnectorClosed) => ctx.notifier.notify().await.err(),
                Ok(_) => None,
            };
            if let Some(e) = error {
                error!(
                    "[Connector::{}] Error shutting down write half of stream {}: {}",
                    ctx.url, stream, e
                );
            }
            stream_sink_tx
                .send(ChannelSinkMsg::RemoveStream(stream))
                .await?;
            Result::Ok(())
        });
    }
}

/// Extract sink specific metadata from event metadata
///
/// The general path is `$<RESOURCE_TYPE>.<ARTEFACT>`
/// Example: `$connector.tcp_server`
fn get_sink_meta<'lt, 'value>(
    meta: &'lt Value<'value>,
    ctx: &SinkContext,
) -> Option<&'lt Value<'value>> {
    ctx.url
        .resource_type()
        .and_then(|rt| meta.get(&Cow::owned(rt.to_string())))
        .and_then(|rt_meta| {
            ctx.url
                .artefact()
                .and_then(|artefact| rt_meta.get(artefact))
        })
}

#[async_trait::async_trait()]
impl<T, F> Sink for ChannelSink<T, F>
where
    T: Hash + Eq + Send + Sync,
    F: (Fn(&Value<'_>) -> Option<T>) + Send + Sync,
{
    /// FIXME: use reply_channel to only ack delivery once it is successfully sent via TCP
    async fn on_event(
        &mut self,
        _input: &str,
        event: Event,
        ctx: &SinkContext,
        serializer: &mut EventSerializer,
        start: u64,
    ) -> ResultVec {
        // clean up
        // make sure channels for the given event are added to avoid stupid errors
        // due to channels not yet handled
        let empty = self.handle_channels_quickly(serializer);
        if empty {
            // no streams available :sob:
            return Ok(vec![SinkReply::Fail, SinkReply::CB(CbAction::Close)]);
        }

        let ingest_ns = event.ingest_ns;
        let stream_ids = event.id.get_streams(ctx.uid);
        trace!("[Sink::{}] on_event stream_ids: {:?}", &ctx.url, stream_ids);

        let contraflow_utils = if event.transactional {
            Some((EventCfData::from(&event), self.reply_tx.clone()))
        } else {
            None
        };

        let mut res = Vec::with_capacity(event.len());
        for (value, meta) in event.value_meta_iter() {
            let mut errored = false;
            let mut found = false;
            let mut remove_streams = vec![];
            // route based on stream id present in event metadata or in event id (trackign the event origin)
            // resolve by checking meta for sink specific metadata
            // fallback: get all tracked stream_ids for the current connector uid
            //
            let streams = self.resolve_stream_from_meta(meta, ctx).map_or_else(
                || {
                    Either::Right(
                        stream_ids
                            .iter()
                            .filter_map(|sid| self.streams.get(sid).map(|sender| (sid, sender))),
                    )
                },
                |stream| Either::Left(std::iter::once(stream)),
            );

            for (stream_id, sender) in streams {
                trace!("[Sink::{}] Send to stream {}.", &ctx.url, stream_id);
                let data = serializer.serialize_for_stream(value, ingest_ns, *stream_id)?;
                let sink_data = SinkData {
                    data,
                    contraflow: contraflow_utils.clone(),
                    start,
                };
                found = true;
                if sender.send(sink_data).await.is_err() {
                    error!(
                        "[Sink::{}] Error sending to closed stream {}.",
                        &ctx.url, stream_id
                    );
                    remove_streams.push(*stream_id);
                    errored = true;
                }
            }

            res.push(if errored || !found {
                SinkReply::Fail
            } else {
                // ack is sent when channel has delivered serialized event asynchronously
                SinkReply::None
            });
            for stream_id in remove_streams {
                trace!("[Sink::{}] Removing stream {}", &ctx.url, stream_id);
                self.remove_stream(stream_id);
                serializer.drop_stream(stream_id);
                // TODO: stream based CB
            }
        }
        Ok(res)
    }

    async fn on_signal(
        &mut self,
        signal: Event,
        _ctx: &SinkContext,
        serializer: &mut EventSerializer,
    ) -> ResultVec {
        if let Some(SignalKind::Tick) = signal.kind {
            self.handle_channels(serializer, true);
        }
        Ok(vec![])
    }

    fn asynchronous(&self) -> bool {
        // events are delivered asynchronously on their stream tasks
        true
    }

    fn auto_ack(&self) -> bool {
        // we handle ack/fail in the asynchronous streams
        false
    }
}