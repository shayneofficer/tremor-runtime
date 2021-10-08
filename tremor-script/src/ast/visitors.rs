// Copyright 2020-2021, The Tremor Team
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

use super::{
    ArrayPattern, ArrayPredicatePattern, BinExpr, Bytes, ClauseGroup, Comprehension, DefaultCase,
    EventPath, Expr, ExprPath, GroupBy, GroupByInt, IfElse, ImutExprInt, Invoke, InvokeAggr, List,
    Literal, LocalPath, Match, Merge, MetadataPath, NodeMetas, Patch, PatchOperation, Path,
    Pattern, PredicateClause, PredicatePattern, Record, RecordPattern, Recur, ReservedPath,
    Segment, StatePath, StrLitElement, StringLit, UnaryExpr,
};

use crate::{
    errors::{error_event_ref_not_allowed, Result},
    registry::mfa,
};

pub(crate) mod group_by_extractor;
pub(crate) mod only_mut_state;
pub(crate) mod target_event_ref;

pub(crate) use group_by_extractor::GroupByExprExtractor;
pub(crate) use target_event_ref::TargetEventRef;

#[derive(Clone, Copy, PartialEq, Eq)]
/// Return value from visit methods for `ImutExprIntVisitor`
/// controlling whether to continue walking the subtree or not
pub enum VisitRes {
    /// carry on walking
    Walk,
    /// stop walking
    Stop,
}

use VisitRes::Walk;

/// Visitor for traversing all `Exprs`s within the given `Exprs`
///
/// Implement your custom expr visiting logic by overwriting the visit_* methods.
/// You do not need to traverse further down. This is done by the provided `walk_*` methods.
/// The walk_* methods implement walking the expression tree, those do not need to be changed.
pub trait ExprVisitor<'script>: ImutExprIntVisitor<'script> {
    /// visit a generic `Expr` (this is called before the concrete `visit_*` method)
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_mexpr(&mut self, e: &mut Expr<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }
    /// entry point into this visitor - call this to start visiting the given expression `e`
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_mexpr(&mut self, e: &mut Expr<'script>) -> Result<()> {
        if self.visit_mexpr(e)? == Walk {
            match e {
                Expr::Match(mmatch) => {
                    if self.visit_mmatch(mmatch.as_mut())? == Walk {
                        self.walk_mmatch(mmatch.as_mut())?
                    }
                }
                Expr::IfElse(ifelse) => {
                    if self.visit_mifelse(ifelse.as_mut())? == Walk {
                        self.walk_mifelse(ifelse.as_mut())?
                    }
                }
                Expr::Assign { path, expr, .. } => {
                    if self.visit_path(path)? == Walk {
                        self.walk_path(path)?;
                    }
                    if self.visit_mexpr(expr.as_mut())? == Walk {
                        self.visit_mexpr(expr.as_mut())?;
                    }
                }
                Expr::AssignMoveLocal { path, .. } => {
                    if self.visit_path(path)? == Walk {
                        self.walk_path(path)?;
                    }
                }
                Expr::Comprehension(c) => todo!(),
                Expr::Drop { mid } => todo!(),
                Expr::Emit(_) => todo!(),
                Expr::Imut(_) => todo!(),
            }
        };
        Ok(())
    }

    /// visit a match expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_mifelse(&mut self, _mifelse: &mut IfElse<'script, Expr<'script>>) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// visit a match expr
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_mifelse(&mut self, mifelse: &mut IfElse<'script, Expr<'script>>) -> Result<()> {
        if self.visit_mifelse(mifelse)? == Walk {
            self.walk_iexpr(&mut mifelse.target)?;
            self.walk_mpredicate_clause(&mut mifelse.if_clause)?;
            self.walk_mdefault_case(&mut mifelse.else_clause)?;
        }
        Ok(())
    }

    /// visit a match expr
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_mdefault_case(&mut self, mdefault: &mut DefaultCase<Expr<'script>>) -> Result<()> {
        if self.walk_mdefault_case(mdefault)? == Walk {
            match mdefault {
                DefaultCase::None | DefaultCase::Null => (),
                DefaultCase::Many { exprs, last_expr } => {
                    for e in exprs {
                        self.walk_mexpr(e)?;
                    }
                    self.walk_mexpr(last_expr)?;
                }
                DefaultCase::One(last_expr) => self.walk_mexpr(last_expr)?,
            }
        }
        Ok(())
    }
    /// visit a match expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_mmatch(&mut self, _mmatch: &mut Match<'script, Expr<'script>>) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// walk a match expr
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_mmatch(&mut self, mmatch: &mut Match<'script, Expr<'script>>) -> Result<()> {
        if self.visit_mmatch(mmatch)? == Walk {
            self.walk_iexpr(&mut mmatch.target)?;
            for group in &mut mmatch.patterns {
                self.walk_mclause_group(group)?;
            }
        }
        Ok(())
    }

    /// visit a group clause
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_mclause_group(
        &mut self,
        group: &mut ClauseGroup<'script, Expr<'script>>,
    ) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// Walks a clause group
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_mclause_group(
        &mut self,
        group: &mut ClauseGroup<'script, Expr<'script>>,
    ) -> Result<()> {
        if self.visit_mclause_group(group)? == Walk {
            match group {
                ClauseGroup::Single {
                    precondition,
                    pattern,
                } => {
                    if let Some(precondition) = precondition {
                        self.walk_precondition(precondition)?;
                    }
                    self.walk_mpredicate_clause(pattern)?;
                }
                ClauseGroup::Simple {
                    precondition,
                    patterns,
                } => {
                    if let Some(precondition) = precondition {
                        self.walk_precondition(precondition)?;
                    }
                    for predicate in patterns {
                        self.walk_mpredicate_clause(predicate)?;
                    }
                }
                ClauseGroup::SearchTree {
                    precondition,
                    tree,
                    rest,
                } => {
                    if let Some(precondition) = precondition {
                        self.walk_precondition(precondition)?;
                    }
                    for (_v, (es, e)) in tree.iter_mut() {
                        for e in es {
                            self.walk_mexpr(e)?;
                        }
                        self.walk_mexpr(e)?;
                    }
                    for predicate in rest {
                        self.walk_mpredicate_clause(predicate)?;
                    }
                }
                ClauseGroup::Combined {
                    precondition,
                    groups,
                } => {
                    if let Some(precondition) = precondition {
                        self.walk_precondition(precondition)?;
                    }
                    for g in groups {
                        self.walk_mclause_group(g)?;
                    }
                }
            }
        };
        Ok(())
    }

    /// visit a predicate clause
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_mpredicate_clause(
        &mut self,
        group: &mut PredicateClause<'script, Expr<'script>>,
    ) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// Walks a predicate clause
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_mpredicate_clause(
        &mut self,
        predicate: &mut PredicateClause<'script, Expr<'script>>,
    ) -> Result<()> {
        if self.visit_mpredicate_clause(predicate)? == Walk {
            self.walk_match_pattern(&mut predicate.pattern)?;
            if let Some(guard) = &mut predicate.guard {
                self.walk_iexpr(guard)?;
            }
            for expr in &mut predicate.exprs {
                self.walk_mexpr(expr)?;
            }
            self.walk_mexpr(&mut predicate.last_expr)?;
        }
        Ok(())
    }
}

/// Visitor for traversing all `ImutExprInt`s within the given `ImutExprInt`
///
/// Implement your custom expr visiting logic by overwriting the visit_* methods.
/// You do not need to traverse further down. This is done by the provided `walk_*` methods.
/// The walk_* methods implement walking the expression tree, those do not need to be changed.
pub trait ImutExprIntVisitor<'script> {
    /// visit a record
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_record(&mut self, _record: &mut Record<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }
    /// walk a record
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_record(&mut self, record: &mut Record<'script>) -> Result<()> {
        if self.visit_record(record)? == Walk {
            for field in &mut record.fields {
                self.walk_string(&mut field.name)?;
                self.walk_iexpr(&mut field.value)?;
            }
        }
        Ok(())
    }
    /// visit a list
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_list(&mut self, _list: &mut List<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }
    /// walk a list
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_list(&mut self, list: &mut List<'script>) -> Result<()> {
        if self.visit_list(list)? == Walk {
            for element in &mut list.exprs {
                self.walk_iexpr(&mut element.0)?;
            }
        }
        Ok(())
    }
    /// visit a binary
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_binary(&mut self, _binary: &mut BinExpr<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }
    /// walk a binary
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_binary(&mut self, binary: &mut BinExpr<'script>) -> Result<()> {
        if self.visit_binary(binary)? == Walk {
            self.walk_iexpr(&mut binary.lhs)?;
            self.walk_iexpr(&mut binary.rhs)?;
        }
        Ok(())
    }

    /// visit a unary expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_unary(&mut self, _unary: &mut UnaryExpr<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }
    /// walk a unary
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_unary(&mut self, unary: &mut UnaryExpr<'script>) -> Result<()> {
        if self.visit_unary(unary)? == Walk {
            self.walk_iexpr(&mut unary.expr)?;
        }
        Ok(())
    }

    /// visit a patch expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_patch(&mut self, _patch: &mut Patch<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// visit a match expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_imatch(&mut self, _mmatch: &mut Match<'script, ImutExprInt>) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// walk a patch expr
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_patch(&mut self, patch: &mut Patch<'script>) -> Result<()> {
        if self.visit_patch(patch)? == Walk {
            self.walk_iexpr(&mut patch.target)?;
            for op in &mut patch.operations {
                match op {
                    PatchOperation::Insert { ident, expr }
                    | PatchOperation::Default { ident, expr }
                    | PatchOperation::Merge { ident, expr }
                    | PatchOperation::Update { ident, expr }
                    | PatchOperation::Upsert { ident, expr } => {
                        self.walk_string(ident)?;
                        self.walk_iexpr(expr)?;
                    }
                    PatchOperation::Copy { from, to } | PatchOperation::Move { from, to } => {
                        self.walk_string(from)?;
                        self.walk_string(to)?;
                    }
                    PatchOperation::Erase { ident } => {
                        self.walk_string(ident)?;
                    }
                    PatchOperation::DefaultRecord { expr }
                    | PatchOperation::MergeRecord { expr } => {
                        self.walk_iexpr(expr)?;
                    }
                }
            }
        }
        Ok(())
    }

    /// visit a match expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_precondition(
        &mut self,
        _precondition: &mut super::ClausePreCondition<'script>,
    ) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// Walks a precondition
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_precondition(
        &mut self,
        precondition: &mut super::ClausePreCondition<'script>,
    ) -> Result<()> {
        if self.visit_precondition(precondition)? == Walk {
            for segment in precondition.path.segments_mut() {
                self.walk_segment(segment)?;
            }
        }
        Ok(())
    }

    /// walk a match expr
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_imatch(&mut self, mmatch: &mut Match<'script, ImutExprInt<'script>>) -> Result<()> {
        if self.visit_imatch(mmatch)? == Walk {
            self.walk_iexpr(&mut mmatch.target)?;
            for group in &mut mmatch.patterns {
                self.walk_iclause_group(group)?;
            }
        }
        Ok(())
    }

    /// visit a match expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_ipredicate_clause(
        &mut self,
        _predicate: &mut PredicateClause<'script, ImutExprInt<'script>>,
    ) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// Walks a predicate clause
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_ipredicate_clause(
        &mut self,
        predicate: &mut PredicateClause<'script, ImutExprInt<'script>>,
    ) -> Result<()> {
        if self.visit_ipredicate_clause(predicate)? == Walk {
            self.walk_match_pattern(&mut predicate.pattern)?;
            if let Some(guard) = &mut predicate.guard {
                self.walk_iexpr(guard)?;
            }
            for expr in &mut predicate.exprs {
                self.walk_iexpr(expr)?;
            }
            self.walk_iexpr(&mut predicate.last_expr)?;
        }
        Ok(())
    }

    /// visit a match expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_iclause_group(
        &mut self,
        _group: &mut ClauseGroup<'script, ImutExprInt<'script>>,
    ) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// Walks a clause group
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_iclause_group(
        &mut self,
        group: &mut ClauseGroup<'script, ImutExprInt<'script>>,
    ) -> Result<()> {
        if self.visit_iclause_group(group)? == Walk {
            match group {
                ClauseGroup::Single {
                    precondition,
                    pattern,
                } => {
                    if let Some(precondition) = precondition {
                        self.walk_precondition(precondition)?;
                    }
                    self.walk_ipredicate_clause(pattern)?;
                }
                ClauseGroup::Simple {
                    precondition,
                    patterns,
                } => {
                    if let Some(precondition) = precondition {
                        self.walk_precondition(precondition)?;
                    }
                    for predicate in patterns {
                        self.walk_ipredicate_clause(predicate)?;
                    }
                }
                ClauseGroup::SearchTree {
                    precondition,
                    tree,
                    rest,
                } => {
                    if let Some(precondition) = precondition {
                        self.walk_precondition(precondition)?;
                    }
                    for (_v, (es, e)) in tree.iter_mut() {
                        for e in es {
                            self.walk_iexpr(e)?;
                        }
                        self.walk_iexpr(e)?;
                    }
                    for predicate in rest {
                        self.walk_ipredicate_clause(predicate)?;
                    }
                }
                ClauseGroup::Combined {
                    precondition,
                    groups,
                } => {
                    if let Some(precondition) = precondition {
                        self.walk_precondition(precondition)?;
                    }
                    for g in groups {
                        self.walk_iclause_group(g)?;
                    }
                }
            }
        };
        Ok(())
    }

    /// visit a match expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_match_pattern(&mut self, _pattern: &mut Pattern<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// walk match patterns
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_match_pattern(&mut self, pattern: &mut Pattern<'script>) -> Result<()> {
        if self.visit_match_pattern(pattern)? == Walk {
            match pattern {
                Pattern::Record(record_pat) => {
                    self.walk_record_pattern(record_pat)?;
                }
                Pattern::Array(array_pat) => {
                    self.walk_array_pattern(array_pat)?;
                }
                Pattern::Expr(expr) => {
                    self.walk_iexpr(expr)?;
                }
                Pattern::Assign(assign_pattern) => {
                    self.walk_match_pattern(assign_pattern.pattern.as_mut())?;
                }
                Pattern::Tuple(tuple_pattern) => {
                    for elem in &mut tuple_pattern.exprs {
                        match elem {
                            ArrayPredicatePattern::Expr(expr) => {
                                self.walk_iexpr(expr)?;
                            }
                            ArrayPredicatePattern::Record(record_pattern) => {
                                self.walk_record_pattern(record_pattern)?;
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// visit a match expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_record_pattern(
        &mut self,
        _record_pattern: &mut RecordPattern<'script>,
    ) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// walk a record pattern
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_record_pattern(&mut self, record_pattern: &mut RecordPattern<'script>) -> Result<()> {
        if self.visit_record_pattern(record_pattern)? == Walk {
            for field in &mut record_pattern.fields {
                match field {
                    PredicatePattern::RecordPatternEq { pattern, .. } => {
                        self.walk_record_pattern(pattern)?;
                    }
                    PredicatePattern::Bin { rhs, .. } => {
                        self.walk_iexpr(rhs)?;
                    }
                    PredicatePattern::ArrayPatternEq { pattern, .. } => {
                        self.walk_array_pattern(pattern)?;
                    }
                    _ => {}
                }
            }
        }
        Ok(())
    }

    /// visit a match expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_array_pattern(
        &mut self,
        array_pattern: &mut ArrayPattern<'script>,
    ) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// walk an array pattern
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_array_pattern(&mut self, array_pattern: &mut ArrayPattern<'script>) -> Result<()> {
        if self.visit_array_pattern(array_pattern)? == Walk {
            for elem in &mut array_pattern.exprs {
                match elem {
                    ArrayPredicatePattern::Expr(expr) => {
                        self.walk_iexpr(expr)?;
                    }
                    ArrayPredicatePattern::Record(record_pattern) => {
                        self.walk_record_pattern(record_pattern)?;
                    }
                    _ => {}
                }
            }
        }
        Ok(())
    }

    /// visit a comprehension
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_comprehension(
        &mut self,
        _comp: &mut Comprehension<'script, ImutExprInt<'script>>,
    ) -> Result<VisitRes> {
        Ok(Walk)
    }
    /// walk a comprehension
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_comprehension(
        &mut self,
        comp: &mut Comprehension<'script, ImutExprInt<'script>>,
    ) -> Result<()> {
        if self.visit_comprehension(comp)? == Walk {
            self.walk_iexpr(&mut comp.target)?;
            for comp_case in &mut comp.cases {
                if let Some(guard) = &mut comp_case.guard {
                    self.walk_iexpr(guard)?;
                }
                for expr in &mut comp_case.exprs {
                    self.walk_iexpr(expr)?;
                }
                self.walk_iexpr(&mut comp_case.last_expr)?;
            }
        }
        Ok(())
    }

    /// visit a merge expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_merge(&mut self, _merge: &mut Merge<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }
    /// walk a merge expr
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_merge(&mut self, merge: &mut Merge<'script>) -> Result<()> {
        if self.visit_merge(merge)? == Walk {
            self.walk_iexpr(&mut merge.target)?;
            self.walk_iexpr(&mut merge.expr)?;
        }
        Ok(())
    }

    /// visit a merge expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_segment(&mut self, _segment: &mut Segment<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// walk a path segment
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_segment(&mut self, segment: &mut Segment<'script>) -> Result<()> {
        if self.visit_segment(segment)? == Walk {
            match segment {
                Segment::Element { expr, .. } => self.walk_iexpr(expr)?,
                Segment::Range {
                    range_start,
                    range_end,
                    ..
                } => {
                    self.walk_iexpr(range_start.as_mut())?;
                    self.walk_iexpr(range_end.as_mut())?;
                }
                Segment::Id { .. } => (),
                Segment::Idx { .. } => (),
            }
        };
        Ok(())
    }

    /// visit a path
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_path(&mut self, _path: &mut Path<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// walk a path
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_path(&mut self, path: &mut Path<'script>) -> Result<()> {
        if self.visit_path(path)? == Walk {
            if let Path::Expr(ExprPath { expr, .. }) = path {
                self.walk_iexpr(expr)?;
            }
            for segment in path.segments_mut() {
                self.walk_segment(segment)?;
            }
        }
        Ok(())
    }

    /// visit a string
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_string(&mut self, _string: &mut StringLit<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// walk a string
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_string(&mut self, string: &mut StringLit<'script>) -> Result<()> {
        if self.visit_string(string)? == Walk {
            for element in &mut string.elements {
                match element {
                    StrLitElement::Lit(l) => todo!(),
                    StrLitElement::Expr(expr) => self.walk_iexpr(expr)?,
                }
            }
        }
        Ok(())
    }

    /// visit a local
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_local(&mut self, _local_idx: &mut usize) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// w a local
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_local(&mut self, local_idx: &mut usize) -> Result<()> {
        self.visit_local(local_idx)?;
        Ok(())
    }

    /// visit a present expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_present(&mut self, _path: &mut Path<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// visit an invoke expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_invoke(&mut self, _invoke: &mut Invoke<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// walk an invoke expr
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_invoke(&mut self, invoke: &mut Invoke<'script>) -> Result<()> {
        if self.visit_invoke(invoke)? == Walk {
            for arg in &mut invoke.args {
                self.walk_iexpr(&mut arg.0)?;
            }
        }
        Ok(())
    }

    /// visit an invoke1 expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_invoke1(&mut self, _invoke: &mut Invoke<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// walk an invoke1 expr
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_invoke1(&mut self, invoke: &mut Invoke<'script>) -> Result<()> {
        if self.visit_invoke1(invoke)? == Walk {
            for arg in &mut invoke.args {
                self.walk_iexpr(&mut arg.0)?;
            }
        }
        Ok(())
    }

    /// visit an invoke2 expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_invoke2(&mut self, _invoke: &mut Invoke<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }
    /// walk an invoke expr
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_invoke2(&mut self, invoke: &mut Invoke<'script>) -> Result<()> {
        if self.visit_invoke2(invoke)? == Walk {
            for arg in &mut invoke.args {
                self.walk_iexpr(&mut arg.0)?;
            }
        }
        Ok(())
    }
    /// visit an invoke3 expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_invoke3(&mut self, _invoke: &mut Invoke<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }
    /// walk an invoke expr
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_invoke3(&mut self, invoke: &mut Invoke<'script>) -> Result<()> {
        if self.visit_invoke3(invoke)? == Walk {
            for arg in &mut invoke.args {
                self.walk_iexpr(&mut arg.0)?;
            }
        }
        Ok(())
    }
    /// visit an `invoke_aggr` expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_invoke_aggr(&mut self, _invoke_aggr: &mut InvokeAggr) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// walk an invoke expr
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_invoke_aggr(&mut self, invoke_aggr: &mut InvokeAggr) -> Result<()> {
        if self.visit_invoke_aggr(invoke_aggr)? == Walk {
            for arg in &mut invoke_aggr.args {
                self.walk_iexpr(&mut arg.0)?;
            }
        }
        Ok(())
    }

    /// visit a recur expr
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_recur(&mut self, _recur: &mut Recur<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }
    /// walk a recur expr
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_recur(&mut self, recur: &mut Recur<'script>) -> Result<()> {
        if self.visit_recur(recur)? == Walk {
            for expr in &mut recur.exprs {
                self.walk_iexpr(&mut expr.0)?;
            }
        }
        Ok(())
    }

    /// visit bytes
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_bytes(&mut self, _bytes: &mut Bytes<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }
    /// walk bytes
    /// # Errors
    /// if the walker function fails
    fn walk_bytes(&mut self, bytes: &mut Bytes<'script>) -> Result<()> {
        if self.visit_bytes(bytes)? == Walk {
            for part in &mut bytes.value {
                self.walk_iexpr(&mut part.data.0)?;
            }
        }
        Ok(())
    }

    /// visit a literal
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_literal(&mut self, _literal: &mut Literal<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// walks a literal
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_literal(&mut self, _literal: &mut Literal<'script>) -> Result<()> {
        self.visit_literal(literal)?;
        Ok(())
    }

    /// visit a generic `ImutExprInt` (this is called before the concrete `visit_*` method)
    ///
    /// # Errors
    /// if the walker function fails
    fn visit_iexpr(&mut self, _e: &mut ImutExprInt<'script>) -> Result<VisitRes> {
        Ok(Walk)
    }

    /// entry point into this visitor - call this to start visiting the given expression `e`
    ///
    /// # Errors
    /// if the walker function fails
    fn walk_iexpr(&mut self, e: &mut ImutExprInt<'script>) -> Result<()> {
        if self.visit_iexpr(e)? == Walk {
            match e {
                ImutExprInt::Record(record) => self.walk_record(record),
                ImutExprInt::List(list) => self.walk_list(list),
                ImutExprInt::Binary(binary) => self.walk_binary(binary.as_mut()),
                ImutExprInt::Unary(unary) => self.walk_unary(unary.as_mut()),
                ImutExprInt::Patch(patch) => self.walk_patch(patch.as_mut()),
                ImutExprInt::Match(mmatch) => self.walk_imatch(mmatch.as_mut()),
                ImutExprInt::Comprehension(comp) => self.walk_comprehension(comp.as_mut()),
                ImutExprInt::Merge(merge) => self.walk_merge(merge.as_mut()),
                ImutExprInt::Path(path) => self.walk_path(path),
                ImutExprInt::String(string) => self.walk_string(string),
                ImutExprInt::Local { idx, .. } => self.walk_local(idx),
                ImutExprInt::Present { path, .. } => self.walk_path(path),
                ImutExprInt::Invoke(invoke) => self.walk_invoke(invoke),
                ImutExprInt::Invoke1(invoke1) => self.walk_invoke1(invoke1),
                ImutExprInt::Invoke2(invoke2) => self.walk_invoke2(invoke2),
                ImutExprInt::Invoke3(invoke3) => self.walk_invoke3(invoke3),
                ImutExprInt::InvokeAggr(invoke_aggr) => self.walk_invoke_aggr(invoke_aggr),
                ImutExprInt::Recur(recur) => self.walk_recur(recur),
                ImutExprInt::Bytes(bytes) => self.walk_bytes(bytes),
                ImutExprInt::Literal(lit) => self.walk_literal(lit),
            }
        } else {
            Ok(())
        }
    }
}

pub(crate) trait GroupByVisitor<'script> {
    fn visit_expr(&mut self, expr: &ImutExprInt<'script>);

    fn walk_group_by(&mut self, group_by: &GroupByInt<'script>) {
        match group_by {
            GroupByInt::Expr { expr, .. } | GroupByInt::Each { expr, .. } => self.visit_expr(expr),
            GroupByInt::Set { items, .. } => {
                for inner_group_by in items {
                    self.walk_group_by(&inner_group_by.0);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::ast::Expr;
    use crate::errors::Result;
    use crate::path::ModulePath;
    use crate::registry::registry;
    use simd_json::prelude::*;

    #[derive(Default)]
    struct Find42Visitor {
        found: usize,
    }

    impl<'script> ImutExprIntVisitor<'script> for Find42Visitor {
        fn visit_literal(&mut self, literal: &mut Literal<'script>) -> Result<VisitRes> {
            if let Some(42) = literal.value.as_u64() {
                self.found += 1;
                return Ok(VisitRes::Stop);
            }
            Ok(VisitRes::Walk)
        }
    }

    fn test_walk<'script>(script: &'script str, expected_42s: usize) -> Result<()> {
        let module_path = ModulePath::load();
        let mut registry = registry();
        crate::std_lib::load(&mut registry);
        let script_script: crate::script::Script =
            crate::script::Script::parse(&module_path, "test", script.to_owned(), &registry)?;
        let script: &crate::ast::Script = script_script.script.suffix();
        let mut imut_expr = script
            .exprs
            .iter()
            .filter_map(|e| {
                if let Expr::Imut(expr) = e {
                    Some(expr)
                } else {
                    None
                }
            })
            .cloned()
            .last()
            .unwrap()
            .into_static();
        let mut visitor = Find42Visitor::default();
        visitor.walk_iexpr(&mut imut_expr)?;
        assert_eq!(
            expected_42s, visitor.found,
            "Did not find {} 42s in {:?}, only {}",
            expected_42s, imut_expr, visitor.found
        );
        Ok(())
    }

    #[test]
    fn test_visitor_walking() -> Result<()> {
        test_walk(
            r#"
            fn hide_the_42(x) with
                x + 1
            end;
            hide_the_42(
                match event.foo of
                  case %{ field == " #{42 + event.foo} ", present foo, absent bar } => event.bar
                  case %[42] => event.snake
                  case a = %(42, ...) => a
                  default => event.snot
                end
            );
        "#,
            3,
        )
    }

    #[test]
    fn test_walk_list() -> Result<()> {
        test_walk(
            r#"
        let x = event.bla + 1;
        fn add(x, y) with
          recur(x + y, 1)
        end;
        let zero = 0;
        [
            -event.foo,
            (patch event of
                insert "snot" => 42,
                merge => {"snot": 42 - zero},
                merge "badger" => {"snot": 42 - zero},
                upsert "snot" => 42,
                copy "snot" => "snotter",
                erase "snotter"
            end),
            (merge event of {"foo": event[42:x]} end),
            "~~~ #{ state[1] } ~~~",
            x,
            x[x],
            add(event.foo, 42),
            <<event.foo:8/unsigned>>
        ]
        "#,
            6,
        )
    }

    #[test]
    fn test_walk_comprehension() -> Result<()> {
        test_walk(
            r#"
            (for group[0] of
              case (i, e) =>
                42 + i
            end
            )
        "#,
            1,
        )
    }
}
