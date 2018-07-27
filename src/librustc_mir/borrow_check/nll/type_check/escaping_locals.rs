// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A MIR walk gathering a union-find of assigned locals, for the purpose of locating the ones
//! escaping into the output.

use rustc::mir::visit::Visitor;
use rustc::mir::*;

use rustc_data_structures::indexed_vec::Idx;
use rustc_data_structures::unify as ut;

crate trait FindEscapingLocals {
    /// Finds all locals ultimately flowing into the output
    /// through assignments.
    fn find_escaping_locals(&self) -> Vec<Local>;
}

impl<'tcx> FindEscapingLocals for Mir<'tcx> {
    fn find_escaping_locals(&self) -> Vec<Local> {
        let mut escaping_locals = Vec::new();

        let mut visitor = GatherAssignedLocalsVisitor::new();
        visitor.visit_mir(self);

        // Check which local ultimately flowed into the output
        let return_place = AssignedLocal(0);
        for (local, _) in self.local_decls.iter_enumerated() {
            if local.index() == 0 {
                continue;
            }

            let assigned_local = AssignedLocal::from(local);
            if visitor
                .unification_table
                .unioned(return_place, assigned_local)
            {
                escaping_locals.push(local);
            }
        }

        escaping_locals
    }
}

/// The MIR visitor gathering the union-find of the locals used in
/// assignments.
struct GatherAssignedLocalsVisitor {
    unification_table: ut::UnificationTable<ut::InPlace<AssignedLocal>>,
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
struct AssignedLocal(u32);

impl ut::UnifyKey for AssignedLocal {
    type Value = ();

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(i: u32) -> AssignedLocal {
        AssignedLocal(i)
    }

    fn tag() -> &'static str {
        "AssignedLocal"
    }
}

impl From<Local> for AssignedLocal {
    fn from(item: Local) -> Self {
        // newtype_indexes use usize but are u32s.
        assert!(item.index() < ::std::u32::MAX as usize);
        AssignedLocal(item.index() as u32)
    }
}

impl GatherAssignedLocalsVisitor {
    fn new() -> Self {
        Self {
            unification_table: ut::UnificationTable::new(),
        }
    }

    fn union_locals_if_needed(&mut self, lvalue: Option<Local>, rvalue: Option<Local>) {
        if let Some(lvalue) = lvalue {
            if let Some(rvalue) = rvalue {
                if lvalue != rvalue {
                    self.unification_table
                        .union(AssignedLocal::from(lvalue), AssignedLocal::from(rvalue));
                }
            }
        }
    }
}

// Returns the potential `Local` associated to this `Place` or `PlaceProjection`
fn find_local_in_place(place: &Place) -> Option<Local> {
    match place {
        Place::Local(local) => Some(*local),
        Place::Projection(proj) => find_local_in_place(&proj.base),
        _ => None,
    }
}

// Returns the potential `Local` in this `Operand`.
fn find_local_in_operand(op: &Operand) -> Option<Local> {
    // Conservatively check a subset of `Operand`s we know our
    // benchmarks track, for example `html5ever`.
    match op {
        Operand::Move(ref place) => find_local_in_place(place),
        _ => None,
    }
}

impl<'tcx> Visitor<'tcx> for GatherAssignedLocalsVisitor {
    fn visit_mir(&mut self, mir: &Mir<'tcx>) {
        // We need as many union-find keys as there are locals
        for _ in 0..mir.local_decls.len() {
            self.unification_table.new_key(());
        }

        self.super_mir(mir);
    }

    fn visit_assign(
        &mut self,
        block: BasicBlock,
        place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        location: Location,
    ) {
        let local = find_local_in_place(place);

        // Conservatively check a subset of `Rvalue`s we know our
        // benchmarks track, for example `html5ever`.
        match rvalue {
            Rvalue::Use(op) => self.union_locals_if_needed(local, find_local_in_operand(op)),
            Rvalue::Ref(_, _, place) => {
                self.union_locals_if_needed(local, find_local_in_place(place))
            }

            Rvalue::Cast(kind, op, _) => match kind {
                CastKind::Unsize => self.union_locals_if_needed(local, find_local_in_operand(op)),
                _ => (),
            },

            Rvalue::Aggregate(_, ops) => {
                for rvalue in ops.iter().map(find_local_in_operand) {
                    self.union_locals_if_needed(local, rvalue);
                }
            }

            _ => (),
        };

        self.super_assign(block, place, rvalue, location);
    }
}
