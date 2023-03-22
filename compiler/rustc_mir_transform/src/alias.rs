mod analysis;
mod optimisation;

use rustc_middle::mir::*;

use rustc_middle::ty::{self, TyCtxt};

use crate::alias::analysis::compute_immutability_spans;

pub struct Alias;

impl<'tcx> MirPass<'tcx> for Alias {
    fn is_enabled(&self, _sess: &rustc_session::Session) -> bool {
        // Require retag statements for this MirPass to run.
        // sess.opts.unstable_opts.mir_emit_retag
        true // (disabling requirement for mir_emit_retag for evaluation)
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let retagged = get_retags(body);
        if retagged.is_empty() {
            return; // Abort pass early, if there is nothing to do.
        }

        let immutability_spans = compute_immutability_spans(tcx, body, retagged, false);

        optimisation::eliminate_reads(tcx, body, immutability_spans);
    }
}

/// Collect places that should be checked by seeing if they are retagged.
/// Rewritten to not use retags for evaluation, because we canot pass `-Zmir-emit-retag` everywhere.
fn get_retags<'tcx>(body: &mut Body<'tcx>) -> Vec<Local> {
    let mut result = Vec::new();
    for arg in body.args_iter() {
        let decl = &body.local_decls[arg];
        if let ty::Ref(_, ty, Mutability::Mut) = decl.ty.kind()
            && ty.is_primitive()
        {
            result.push(arg)
        }
    }

    result
}
