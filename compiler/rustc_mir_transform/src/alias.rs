use crate::MirPass;
use itertools::Either;
use rustc_index::vec::IndexVec;
use rustc_middle::mir::{
    BasicBlock, Body, Local, Location, Operand, RetagKind, Rvalue, StatementKind,
};
use rustc_middle::ty::TyCtxt;
use tracing::trace;

pub struct Alias;

// Notes
// std::env::set_var("RUSTC_LOG", "debug");
// std::env::remove_var("RUSTC_LOG");

impl<'tcx> MirPass<'tcx> for Alias {
    // Require retags for this MirPass to run.
    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        sess.opts.debugging_opts.mir_emit_retag
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        // Temporary for debugging (Helps to only println for the target file)
        let def_id = body.source.def_id();
        let path = tcx.def_path_str(def_id);
        if !path.contains("move_up") {
            return;
        }

        trace!("Some Trace!");
        println!("Path: {}", path);
        println!("Blocks:");
        for (id, block) in body.basic_blocks().iter_enumerated() {
            println!("{:?}", id);
            println!("Next: {:?}", block.terminator().successors().collect::<Vec<_>>());
            println!("{:#?}", block);
            println!();
        }

        // Collect places that should be checked by seeing if they are retagged.
        let mut retagged = Vec::new();
        let mut write_locations = Vec::new();
        let Some(bb0) = body.basic_blocks().indices().nth(0) else {
            return; // Stop pass if there are no basic blocks
        };
        let first_basic_block = &body.basic_blocks()[bb0];
        for (stmt_idx, stmt) in first_basic_block.statements.iter().enumerate() {
            if let StatementKind::Retag(RetagKind::FnEntry, place) = &stmt.kind {
                retagged.push(place.local);
                write_locations.push(Location { block: bb0, statement_index: stmt_idx });
            }
        }

        println!("Retagged: {:?}", retagged);
        println!();

        // Traverse CFG to compute last write access per interesting place.
        let mut last_writes = create_bb_indexed_vec(body.basic_blocks().len(), write_locations);
        let mut visited = create_bb_indexed_vec(body.basic_blocks().len(), false);

        let mut block_stack = vec![bb0];
        visited[bb0] = true;

        while !block_stack.is_empty() {
            let current_basic_block = block_stack.pop().unwrap(); // ok, because of the is_empty check

            let block_data = &body.basic_blocks()[current_basic_block];
            let statements_len = block_data.statements.len();

            let mut location: Location = current_basic_block.start_location();
            while location.statement_index <= statements_len {
                let reads = reads_stmt(body, location, &retagged);
                {
                    // Debug only
                    println!("{:?}", body.stmt_at(location));
                    println!("Reads: {:?}", reads);
                }

                let read_idx = index_of_access(reads, &retagged);
                if let Some(read_idx) = read_idx {
                    let last_write = last_writes[current_basic_block][read_idx];
                    if last_write.block == current_basic_block {
                        // Found read after write in the same basic block.
                        // If the write was a constant it can always be replaced directly,
                        // because there can never be jumps into the middle of a basic block.
                        if let Some(constant_operand) =
                            write_is_assigning_constant(body, last_write)
                        {
                            replace_read_with_constant(body, location, constant_operand);
                            {
                                // Debug only
                                println!("New Stmt: {:?}", body.stmt_at(location));
                            }
                        }
                    }
                }

                let writes = writes_stmt(body, location, &retagged);
                let write_idx = index_of_access(writes, &retagged);
                if let Some(write_idx) = write_idx {
                    last_writes[current_basic_block][write_idx] = location;
                }
                location = location.successor_within_block();
                {
                    // Debug only
                    println!("Writes: {:?}", writes);
                    println!();
                }
            }

            // Visit sucessor basic blocks in the CFG.
            let block_data = &body.basic_blocks()[current_basic_block];
            for &successor in block_data.terminator().successors() {
                if !visited[successor] {
                    visited[successor] = true;
                    block_stack.push(successor);
                }
            }
        }

        println!("Blocks After:");
        for (id, block) in body.basic_blocks().iter_enumerated() {
            println!("{:?}", id);
            println!("{:#?}", block);
            println!();
        }

        // Make stdout visible by emitting an error.
        tcx.sess.err(&format!("Path: {}", path));
    }
}

fn index_of_access(access: Option<Local>, refs: &[Local]) -> Option<usize> {
    access.map(|read| {
        refs.iter()
            .enumerate()
            .find_map(|(i, &local)| if local == read { Some(i) } else { None })
            .expect("found access to local that was not searched for")
    })
}

fn create_bb_indexed_vec<T: Clone>(size: usize, default: T) -> IndexVec<BasicBlock, T> {
    let mut result = IndexVec::with_capacity(size);
    result.extend((0..size).map(|_| default.clone()));
    result
}

fn reads_stmt<'tcx>(body: &Body<'tcx>, location: Location, refs: &[Local]) -> Option<Local> {
    let stmt = body.stmt_at(location);
    match stmt {
        Either::Left(stmt) => match &stmt.kind {
            StatementKind::Assign(assign) => reads_rvalue(body, &assign.1, refs),
            StatementKind::FakeRead(_) => None,
            StatementKind::SetDiscriminant { .. /* place, variant_index */ } => None,
            StatementKind::StorageLive(_) => None,
            StatementKind::StorageDead(_) => None,
            StatementKind::Retag(_, _) => None,
            StatementKind::AscribeUserType(_, _) => None,
            StatementKind::Coverage(_) => None,
            StatementKind::CopyNonOverlapping(_) => None,
            StatementKind::Nop => None,
        },
        Either::Right(_) => None,
    }
}

fn reads_rvalue<'tcx>(_body: &Body<'tcx>, rvalue: &Rvalue<'tcx>, refs: &[Local]) -> Option<Local> {
    match rvalue {
        Rvalue::Use(operand) => reads_operand(operand, refs),
        Rvalue::Repeat(_, _) => None,
        Rvalue::Ref(_, _, _) => None,
        Rvalue::ThreadLocalRef(_) => None,
        Rvalue::AddressOf(_, _) => None,
        Rvalue::Len(_) => None,
        Rvalue::Cast(_, _, _) => None,
        Rvalue::BinaryOp(_, _) => None,
        Rvalue::CheckedBinaryOp(_, _) => None,
        Rvalue::NullaryOp(_, _) => None,
        Rvalue::UnaryOp(_, _) => None,
        Rvalue::Discriminant(_) => None,
        Rvalue::Aggregate(_, _) => None,
        Rvalue::ShallowInitBox(_, _) => None,
    }
}

fn reads_operand<'tcx>(operand: &Operand<'tcx>, refs: &[Local]) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => local_in_locals(place.local, refs),
        Operand::Constant(_) => None,
    }
}

fn writes_stmt<'tcx>(body: &Body<'tcx>, location: Location, refs: &[Local]) -> Option<Local> {
    let stmt = body.stmt_at(location);
    match stmt {
        Either::Left(stmt) => match &stmt.kind {
            StatementKind::Assign(assign) => local_in_locals(assign.0.local, refs),
            _ => None,
        },
        Either::Right(_) => None,
    }
}

fn local_in_locals(local: Local, locals: &[Local]) -> Option<Local> {
    locals.iter().find(|&&l| l == local).map(Local::clone)
}

fn write_is_assigning_constant<'tcx>(
    body: &Body<'tcx>,
    location: Location,
) -> Option<Operand<'tcx>> {
    let stmt = body.stmt_at(location);
    match stmt {
        Either::Left(stmt) => match &stmt.kind {
            StatementKind::Assign(assign) => rvalue_is_constant(body, &assign.1),
            _ => None,
        },
        Either::Right(_) => None,
    }
}

fn rvalue_is_constant<'tcx>(_body: &Body<'tcx>, rvalue: &Rvalue<'tcx>) -> Option<Operand<'tcx>> {
    match rvalue {
        Rvalue::Use(operand) => match operand {
            Operand::Constant(_) => Some(operand.clone()),
            _ => None,
        },
        _ => None,
    }
}

fn replace_read_with_constant<'tcx>(
    body: &mut Body<'tcx>,
    location: Location,
    constant: Operand<'tcx>,
) {
    let block = &mut body.basic_blocks_mut()[location.block];
    if location.statement_index < block.statements.len() {
        // Replace statement
        let statement = &mut block.statements[location.statement_index];
        match &mut statement.kind {
            StatementKind::Assign(assign) => assign.1 = Rvalue::Use(constant),
            _ => {}
        }
    } else {
        // Replace terminator
        todo!();
    }
}
