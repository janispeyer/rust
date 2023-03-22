use rustc_middle::{
    mir::{
        Body, LocalDecl, Location, Operand, Place, ProjectionElem, Rvalue, Statement, StatementKind,
    },
    ty::{List, TyCtxt},
};

use crate::alias::analysis::{ImmutabilitySpan, ImmutabilitySpans};

pub fn eliminate_reads<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    immutability_spans: ImmutabilitySpans,
) {
    EliminateReadsOptimisation { tcx, body, assignments: Vec::new() }.run(immutability_spans);
}

struct EliminateReadsOptimisation<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    body: &'a mut Body<'tcx>,
    assignments: Vec<(Location, Statement<'tcx>)>,
}

impl<'tcx, 'a> EliminateReadsOptimisation<'tcx, 'a> {
    pub fn run(mut self, immutability_spans: ImmutabilitySpans) {
        // Sorting by location ensures deterministic output.
        let mut immutability_spans: Vec<_> = immutability_spans.into_iter().collect();
        immutability_spans.sort_unstable_by(|(a, _), (b, _)| a.cmp(b));

        for (location, span) in immutability_spans {
            self.eliminate_reads_span(location, span);
        }

        // Add back assignments that were replaced.
        // This will make previously calculated locations invalid,
        // which is also why we need to start at the bottom.
        let mut assignments = self.assignments;
        assignments.sort_unstable_by(|(a, _), (b, _)| b.cmp(a));
        for (location, assignment) in assignments {
            let statements = &mut self.body[location.block].statements;
            statements.insert(location.statement_index + 1, assignment);
        }
    }

    fn eliminate_reads_span(&mut self, location: Location, span: ImmutabilitySpan) {
        // Get original assignment.
        let basic_blocks = self.body.basic_blocks.as_mut();
        let statement = &basic_blocks[location.block].statements[location.statement_index];
        let StatementKind::Assign(ref assignment) = statement.kind else {
            panic!("ImmutabiltySpan always has to start at an assignment, but was given one that starts wih {:?}", statement);
        };

        let assignment_ty = assignment.0.ty(&self.body.local_decls, self.tcx).ty;
        let internal_local =
            self.body.local_decls.push(LocalDecl::new(assignment_ty, self.body.span));
        let internal_place = Place { local: internal_local, projection: List::empty() };
        let internal_rvalue = Rvalue::Use(Operand::Copy(internal_place));
        let mut rvalue_used = false;

        // Search for reads of `*x` and replace them with `internal_rvalue`.
        for span_location in span.1 {
            let statement = self.body.stmt_at(span_location);
            let Some(StatementKind::Assign(assignment)) = statement.left().map(|s| &s.kind) else {
                continue;
            };

            let Rvalue::Use(Operand::Copy(place)) = assignment.1 else {
                continue;
            };

            if span.0 != place.local {
                continue;
            }

            let [ProjectionElem::Deref] = place.projection.as_slice() else {
                continue;
            };

            // At this point we know that the statement is an assignment of the form `? = (*x)`
            // and we can replace `(*x)` with `internal`.
            let statements = &mut self.body[span_location.block].statements;
            let statement = &mut statements[span_location.statement_index];
            let StatementKind::Assign(assignment) = &mut statement.kind else {
                unreachable!();
            };
            assignment.1 = internal_rvalue.clone();
            rvalue_used = true;
        }

        if !rvalue_used {
            self.body.local_decls.pop();
        } else {
            // Swap assignment of kind `(*x) = rvalue` with `internal = rvalue`.
            // This is only done when we replaced reads of `*x` with `internal` where apropriate.
            let basic_blocks = self.body.basic_blocks.as_mut();
            let mut statement =
                &mut basic_blocks[location.block].statements[location.statement_index];
            let mut original_statement = statement.replace_nop();
            let StatementKind::Assign(mut assignment) = original_statement.kind else {
                unreachable!()
            };

            let rvalue = std::mem::replace(&mut assignment.1, internal_rvalue.clone());
            statement.kind = StatementKind::Assign(Box::new((internal_place, rvalue)));
            original_statement.kind = StatementKind::Assign(assignment);
            self.assignments.push((location, original_statement));
        }
    }
}
