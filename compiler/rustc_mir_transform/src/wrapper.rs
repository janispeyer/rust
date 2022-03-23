use std::borrow::Cow;

use crate::{MirPass, MirPhase, MIR_PASS_INJECTION};
use rustc_middle::{mir::Body, ty::TyCtxt};

pub struct Wrapper;

impl<'tcx> MirPass<'tcx> for Wrapper {
    fn name(&self) -> Cow<'_, str> {
        match &*MIR_PASS_INJECTION.lock().unwrap() {
            Some(pass) => Cow::Owned(pass.name().into_owned()),
            None => Cow::from("WrapperEmpty"),
        }
    }

    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        MIR_PASS_INJECTION
            .lock()
            .unwrap()
            .as_ref()
            .map(|pass| pass.is_enabled(sess))
            .unwrap_or(false)
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        if let Some(pass) = &*MIR_PASS_INJECTION.lock().unwrap() {
            pass.run_pass(tcx, body);
        }
    }

    fn phase_change(&self) -> Option<MirPhase> {
        MIR_PASS_INJECTION.lock().unwrap().as_ref().and_then(|pass| pass.phase_change())
    }

    fn is_mir_dump_enabled(&self) -> bool {
        MIR_PASS_INJECTION
            .lock()
            .unwrap()
            .as_ref()
            .map(|pass| pass.is_mir_dump_enabled())
            .unwrap_or(false)
    }
}
