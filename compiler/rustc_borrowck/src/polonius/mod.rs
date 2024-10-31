#![allow(rustc::potential_query_instability)]

use std::collections::BTreeSet;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_index::bit_set::SparseBitMatrix;
use rustc_middle::mir::{
    Body, Local, Location, Place, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
};
use rustc_middle::ty::{RegionVid, TyCtxt, Variance};
use rustc_mir_dataflow::points::PointIndex;

use crate::constraints::{
    LocalizedConstraintGraph, LocalizedOutlivesConstraint, LocalizedOutlivesConstraintSet,
    LocalizedRegionVid, OutlivesConstraintSet,
};
use crate::dataflow::BorrowIndex;
use crate::region_infer::values::LivenessValues;
use crate::type_check::Locations;
use crate::universal_regions::UniversalRegions;
use crate::visit::Visitor;
use crate::{BorrowSet, PlaceConflictBias, RegionInferenceContext, places_conflict};

pub(crate) mod legacy;

pub(crate) fn create_localized_constraints<'tcx>(
    regioncx: &mut RegionInferenceContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    localized_outlives_constraints: &mut LocalizedOutlivesConstraintSet,
) {
    if !tcx.sess.opts.unstable_opts.polonius.is_next_enabled() {
        return;
    }

    // Convert constraints
    convert_typeck_constraints(
        tcx,
        body,
        &regioncx.liveness_constraints,
        &regioncx.constraints,
        regioncx.universal_regions(),
        localized_outlives_constraints,
    );
    convert_liveness_constraints(
        tcx,
        body,
        &regioncx.liveness_constraints,
        localized_outlives_constraints,
    );

    // TMP: dump localized constraints as a mermaid graph
    {
        // TMP: we need to incorporate kills in the constraints or the graph itself, so that
        // traversal takes them into account. Until then hack this in the dataviz so that we can
        // debug the failing test cases.
        let mut kills = Kills { borrow_set, tcx, body, kills: FxHashMap::default() };
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            kills.visit_basic_block_data(bb, data);
        }

        dump_mermaid_graph(
            borrow_set,
            &regioncx.liveness_constraints,
            localized_outlives_constraints,
            &kills.kills,
        );
    }

    // ---

    // TMP: compute points where loans are live from reachability and store that as the live loans
    // that the scope computation uses in dataflow.
    let graph = LocalizedConstraintGraph::new(localized_outlives_constraints);
    for (loan_idx, loan) in borrow_set.iter_enumerated() {
        let node = LocalizedRegionVid {
            region: loan.region,
            point: regioncx.liveness_constraints.point_from_location(loan.reserve_location),
        };

        for succ in graph.all_successors(node) {
            // FIXME: check off-by-one check, the loan should indeed only be live at the successor
            // of where it's introduced.
            if succ.point == node.point {
                continue;
            }

            if regioncx
                .liveness_constraints
                .loans
                .as_ref()
                .unwrap()
                .live_regions
                .contains(succ.point, succ.region)
                || regioncx.is_region_live_at_all_points(succ.region)
            {
                let loans = regioncx.liveness_constraints.loans.as_mut().unwrap();
                let live_loans = &mut loans.live_loans2;
                live_loans.insert(succ.point, loan_idx);
            }
        }
    }
}

/// Convert constraints from typeck, propagating loans throught subsets, at a single point.
pub(crate) fn convert_typeck_constraints<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    liveness: &LivenessValues,
    outlives_constraints: &OutlivesConstraintSet<'_>,
    universal_regions: &UniversalRegions<'tcx>,
    localized_outlives_constraints: &mut LocalizedOutlivesConstraintSet,
) {
    for outlives_constraint in outlives_constraints.outlives() {
        let current_location = match outlives_constraint.locations {
            // FIXME: for now, turn logical constraints holding at all points into physical edges at every point in the graph.
            Locations::All(_span) => {
                for (block, bb) in body.basic_blocks.iter_enumerated() {
                    let statement_count = bb.statements.len();
                    for statement_index in 0..=statement_count {
                        let current_location = Location { block, statement_index };
                        let current_point = liveness.point_from_location(current_location);

                        localized_outlives_constraints.push(LocalizedOutlivesConstraint {
                            source: outlives_constraint.sup,
                            from: current_point,
                            target: outlives_constraint.sub,
                            to: current_point,
                            tag: "TR0",
                        });
                    }
                }

                continue;
            }
            Locations::Single(location) => location,
        };
        let current_point = liveness.point_from_location(current_location);

        // Note: statements initializing a local need to be handled with care:
        // - the local is dead on entry but will be live on exit / on entry to the successor points.
        //   We therefore can't rely on liveness to propagate the loans to the successors, and we do
        //   it here by flowing to the successor points.
        // - the outlives constraints therefore flow from the types on entry to the type of the place on output
        //
        // This happens for assignments and terminators.

        // 1. terminators, but `Call`s are the most important
        let Some(stmt) =
            &body[current_location.block].statements.get(current_location.statement_index)
        else {
            debug_assert_eq!(
                current_location.statement_index,
                body[current_location.block].statements.len()
            );
            let terminator = body[current_location.block].terminator();

            let tag = match &terminator.kind {
                rustc_middle::mir::TerminatorKind::Call { destination, target, .. } => {
                    // If there is a target for the call we also relate what flows into the
                    // destination here to entry to that successor.
                    // FIXME: this feels incomplete/fishy. Compare NLL tests that exercise these
                    // here, including calls that diverge.
                    if let Some(target_block) = target {
                        let next_location = Location { block: *target_block, statement_index: 0 };
                        let next_point = liveness.point_from_location(next_location);

                        // FIXME: ensure typeck has created the possible constraints dealing with
                        //        the call arguments: we shouldn't need to care about variance here
                        // FIXME: compared to assignments, there shouldn't be constraints that don't
                        //        flow into the destination here, but make sure that's the case
                        //        because we'll just redirect flowing into the subregion to the
                        //        regions in the destination at the target location.
                        let destination_ty = destination.ty(&body.local_decls, tcx);
                        tcx.for_each_free_region(&destination_ty, |live_region| {
                            let live_region = universal_regions.to_region_vid(live_region);
                            localized_outlives_constraints.push(LocalizedOutlivesConstraint {
                                source: outlives_constraint.sub,
                                from: current_point,
                                target: live_region,
                                to: next_point,
                                tag: "TR1C1A",
                            });
                        });

                        "TR1C1A"
                    } else {
                        "TR1C1B"
                    }
                }
                rustc_middle::mir::TerminatorKind::Goto { .. } => "TR1C2",
                rustc_middle::mir::TerminatorKind::SwitchInt { .. } => "TR1C3",
                rustc_middle::mir::TerminatorKind::UnwindResume => "TR1C4",
                rustc_middle::mir::TerminatorKind::UnwindTerminate(_) => "TR1C5",
                rustc_middle::mir::TerminatorKind::Return => "TR1C6",
                rustc_middle::mir::TerminatorKind::Unreachable => "TR1C7",
                rustc_middle::mir::TerminatorKind::Drop { .. } => "TR1C8",
                rustc_middle::mir::TerminatorKind::Assert { .. } => "TR1C9",
                rustc_middle::mir::TerminatorKind::Yield { .. } => "TR1C10",
                rustc_middle::mir::TerminatorKind::CoroutineDrop => "TR1C11",
                rustc_middle::mir::TerminatorKind::FalseEdge { .. } => "TR1C12",
                rustc_middle::mir::TerminatorKind::FalseUnwind { .. } => "TR1C13",
                rustc_middle::mir::TerminatorKind::InlineAsm { .. } => "TR1C14",
                rustc_middle::mir::TerminatorKind::TailCall { .. } => "TR1C15",
            };

            localized_outlives_constraints.push(LocalizedOutlivesConstraint {
                source: outlives_constraint.sup,
                from: current_point,
                target: outlives_constraint.sub,
                to: current_point,
                tag,
            });

            continue;
        };

        // Assert that no regions present in the RHS of an assignment flow into themselves in the LHS.
        if let StatementKind::Assign(box (dest, src)) = &stmt.kind {
            // To create localized outlives without mid-points, we rely on the property that no input
            // regions from the RHS of the assignment will flow into themselves: they should not
            // appear in the output regions in the LHS.
            //
            // We believe this to be true by construction of the MIR, via temporaries, and assert it
            // here.
            //
            // We think we can get away without midpoints because:
            // - every LHS Place has a unique set of regions that don't appear elsewhere
            // - this implies that for them to be part of the RHS, the same Place must be read and
            //   written
            // - and THAT should be UB in MIR
            assert!(
                {
                    let mut lhs_regions = FxHashSet::default();
                    tcx.for_each_free_region(dest, |region| {
                        let region = universal_regions.to_region_vid(region);
                        lhs_regions.insert(region);
                    });

                    let mut rhs_regions = FxHashSet::default();
                    tcx.for_each_free_region(src, |region| {
                        let region = universal_regions.to_region_vid(region);
                        rhs_regions.insert(region);
                    });

                    // The intersection between LHS and RHS regions should be empty.
                    let mut common_regions = lhs_regions.intersection(&rhs_regions);
                    common_regions.next().is_none()
                },
                "there should be no common regions between the LHS and RHS of a statement"
            );
        }

        // Propagate loans from the source to the target at the constraint's location.
        if let StatementKind::Assign(box (lhs, _rhs)) = &stmt.kind {
            // We should be tracking these better upstream but: we want to relate the types on entry
            // to the type of the place on exit.
            // That is, outlives constraint on the RHS are on entry, and outlives constraints to the
            // LHS are on exit (i.e. on entry to the successor location).

            // For a given `sup -> sub` constraint, we only need to check whether the sub region is
            // one of the free regions of the LHS' type (or the opposite via the RHS'). If it is,
            // the current constraint is an outlives constraint to the type on exit, which we turn
            // into a constraint to the type on entry of the successor point.
            let mut to = current_point;
            let lhs_ty = body.local_decls[lhs.local].ty;

            // FIXME: do we need to use `for_liveness::FreeRegionsVisitor` here to automatically
            // handle aliases?
            tcx.for_each_free_region(&lhs_ty, |region| {
                let region = universal_regions.to_region_vid(region);
                if region == outlives_constraint.sub {
                    let next_location = Location {
                        block: current_location.block,
                        statement_index: current_location.statement_index + 1,
                    };
                    to = liveness.point_from_location(next_location);
                }
            });

            localized_outlives_constraints.push(LocalizedOutlivesConstraint {
                source: outlives_constraint.sup,
                from: current_point,
                target: outlives_constraint.sub,
                to,
                tag: if to == current_point { "TR2" } else { "TR3" },
            });
        } else {
            // The default case, we localize an outlives constraint to where it arises.
            localized_outlives_constraints.push(LocalizedOutlivesConstraint {
                source: outlives_constraint.sup,
                from: current_point,
                target: outlives_constraint.sub,
                to: current_point,
                tag: "TR4",
            });
        }
    }
}

/// Propagate loans throughout the CFG: for each statement in the MIR, create localized outlives
/// constraints for loans that are propagated to the next statements.
pub(crate) fn convert_liveness_constraints<'tcx>(
    _tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    liveness: &LivenessValues,
    localized_outlives_constraints: &mut LocalizedOutlivesConstraintSet,
) {
    let live_loans =
        liveness.loans.as_ref().expect("Loan liveness data is only present with `-Zpolonius=next`");
    let live_regions = &live_loans.live_regions;
    let live_region_variances = &live_loans.live_region_variances;

    for (block, bb) in body.basic_blocks.iter_enumerated() {
        let statement_count = bb.statements.len();
        for statement_index in 0..=statement_count {
            let current_location = Location { block, statement_index };
            let current_point = liveness.point_from_location(current_location);

            if statement_index != statement_count {
                // Intra-block edges, straight line constraints from each point to its successor
                // within the same block.
                let next_location = Location { block, statement_index: statement_index + 1 };
                let next_point = liveness.point_from_location(next_location);
                propagate_loans_between_points(
                    live_regions,
                    current_point,
                    next_point,
                    localized_outlives_constraints,
                    live_region_variances,
                    liveness,
                );
            } else {
                // Inter-block edges, from the block's terminator to each successor block's entry
                // point.
                for successor_block in bb.terminator().successors() {
                    let next_location = Location { block: successor_block, statement_index: 0 };
                    let next_point = liveness.point_from_location(next_location);
                    propagate_loans_between_points(
                        live_regions,
                        current_point,
                        next_point,
                        localized_outlives_constraints,
                        live_region_variances,
                        liveness,
                    );
                }
            }
        }
    }
}

/// Propagate loans within a region between two points in the CFG, if that region is live at both
/// the source and target points.
///
/// For each region in `current_live_regions`, the regions live at the `current_point`, if that
/// region is live at the `next_point`, we add a localized outlives constraint between the two.
fn propagate_loans_between_points(
    live_regions: &SparseBitMatrix<PointIndex, RegionVid>,
    current_point: PointIndex,
    next_point: PointIndex,
    localized_outlives_constraints: &mut LocalizedOutlivesConstraintSet,
    live_region_variances: &FxHashMap<RegionVid, FxHashSet<Variance>>,
    _liveness: &LivenessValues,
) {
    let Some(current_live_regions) = live_regions.row(current_point) else {
        // There are no constraints to add: there are no live regions at the current point.
        return;
    };
    let Some(next_live_regions) = live_regions.row(next_point) else {
        // There are no constraints to add: there are no live regions at the next point.
        return;
    };

    for region in next_live_regions.iter() {
        if !current_live_regions.contains(region) {
            continue;
        }

        // `region` is indeed live at both points, add a constraint between them, according to variance.

        // FIXME: No recorded variance found here. Defaulting to covariant for now. Fix this.
        let Some(variances) = live_region_variances.get(&region) else {
            add_liveness_constraint_for_variance(
                region,
                current_point,
                next_point,
                Variance::Covariant,
                localized_outlives_constraints,
                Some("LR0"),
            );

            continue;
        };

        for variance in variances {
            add_liveness_constraint_for_variance(
                region,
                current_point,
                next_point,
                *variance,
                localized_outlives_constraints,
                None,
            );
        }
    }
}

fn add_liveness_constraint_for_variance(
    region: RegionVid,
    current_point: PointIndex,
    next_point: PointIndex,
    variance: Variance,
    localized_outlives_constraints: &mut LocalizedOutlivesConstraintSet,
    tag: Option<&'static str>,
) {
    match variance {
        Variance::Covariant => {
            // The regular direction, from the current point to the next point
            localized_outlives_constraints.push(LocalizedOutlivesConstraint {
                source: region,
                from: current_point,
                target: region,
                to: next_point,
                tag: tag.unwrap_or("LR1"),
            });
        }
        Variance::Contravariant => {
            // Inverse direction, from the next point to the current point
            localized_outlives_constraints.push(LocalizedOutlivesConstraint {
                source: region,
                from: next_point,
                target: region,
                to: current_point,
                tag: tag.unwrap_or("LR2"),
            });
        }
        Variance::Invariant => {
            // We add both directional edges
            localized_outlives_constraints.push(LocalizedOutlivesConstraint {
                source: region,
                from: current_point,
                target: region,
                to: next_point,
                tag: tag.unwrap_or("LR3"),
            });
            localized_outlives_constraints.push(LocalizedOutlivesConstraint {
                source: region,
                from: next_point,
                target: region,
                to: current_point,
                tag: tag.unwrap_or("LR3"),
            });
        }
        Variance::Bivariant => {
            // We don't add any edges
        }
    }
}

fn dump_mermaid_graph<'tcx>(
    borrow_set: &BorrowSet<'tcx>,
    liveness: &LivenessValues,
    localized_outlives_constraints: &LocalizedOutlivesConstraintSet,
    kills: &FxHashMap<Location, BTreeSet<BorrowIndex>>,
) {
    eprintln!("flowchart TD");

    // Loans subgraph
    eprintln!("    subgraph \"Loans\"");
    for loan_idx in 0..borrow_set.len() {
        eprintln!("        L{loan_idx}");
    }
    eprintln!("    end");
    eprintln!();

    let location_name = |location: Location| {
        // A location looks like `bb5[2]`. As that is not a syntactically valid mermaid node id,
        // transform it into `BB5_2`.
        format!("BB{}_{}", location.block.index(), location.statement_index)
    };
    let point_name = |point: PointIndex| {
        let location = liveness.location_from_point(point);
        location_name(location)
    };
    let region_name = |region: RegionVid| format!("'{}", region.index());

    for (loan_idx, loan) in borrow_set.iter_enumerated() {
        let region = loan.region;
        let location = loan.reserve_location;
        eprintln!(
            "    L{} --> {}_{}",
            loan_idx.index(),
            region_name(region),
            location_name(location)
        );
    }
    eprintln!();

    let mut points_per_region: FxHashMap<RegionVid, FxHashSet<PointIndex>> = FxHashMap::default();
    for constraint in &localized_outlives_constraints.outlives {
        points_per_region.entry(constraint.source).or_default().insert(constraint.from);
        points_per_region.entry(constraint.target).or_default().insert(constraint.to);
    }

    // Regions subgraphs
    for (region, points) in points_per_region {
        eprintln!("    subgraph \"{}\"", region_name(region));
        for point in points {
            eprintln!("        {}_{}", region_name(region), point_name(point));

            // let live_regions_at = liveness.points.as_ref().unwrap();
            // let is_region_live_at_point = live_regions_at.contains(region, point);
            // if !is_region_live_at_point {
            //     eprintln!(
            //         "        style {}_{} opacity:0.6",
            //         region_name(region),
            //         point_name(point)
            //     );
            // }
        }
        eprintln!("    end");
        eprintln!();
    }

    // Subset graph
    for constraint in &localized_outlives_constraints.outlives {
        let kills_at_source = kills.get(&liveness.location_from_point(constraint.from));

        // For the edge labe, show tag only if there are no kills, or if there are kills at this
        // point, tag + kills; only on constraints leaving the point
        let edge_label = if kills_at_source.is_none()
            || kills_at_source
                .is_some_and(|kills| kills.is_empty() || constraint.from == constraint.to)
        {
            constraint.tag.to_string()
        } else {
            use std::fmt::Write;
            let mut s = format!("{}, kills ", constraint.tag);
            let kills = kills_at_source.unwrap();
            for (idx, kill) in kills.iter().enumerate() {
                let sep = if idx < kills.len() - 1 { ", " } else { "" };
                let _ = write!(s, "L{}{sep}", kill.as_u32());
            }
            s
        };
        eprintln!(
            "    {}_{} -- {} --> {}_{}",
            region_name(constraint.source),
            point_name(constraint.from),
            edge_label,
            region_name(constraint.target),
            point_name(constraint.to),
        )
    }

    // // ---
    // // Dump loan reachabilility
    // let graph = LocalizedConstraintGraph::new(&localized_outlives_constraints);
    // for (loan_idx, loan) in borrow_set.iter_enumerated() {
    //     eprintln!();

    //     let node = LocalizedRegionVid {
    //         region: loan.region,
    //         point: liveness.point_from_location(loan.reserve_location),
    //     };
    //     for succ in graph.all_successors(node) {
    //         eprintln!(
    //             "loan {loan_idx:?} (introduced at: {:?}_{}) reaches {:?}_{}, target origin is live at that point: {:?} (live origins: {:?})",
    //             node.region,
    //             point_name(node.point),
    //             succ.region,
    //             point_name(succ.point),
    //             liveness.loans.as_ref().unwrap().live_regions.contains(succ.point, succ.region),
    //             liveness.loans.as_ref().unwrap().live_regions.iter(succ.point).collect::<Vec<_>>(),
    //         );
    //     }
    // }
}

struct Kills<'a, 'tcx> {
    body: &'a Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    borrow_set: &'a BorrowSet<'tcx>,

    /// The set of loans killed at each location
    kills: FxHashMap<Location, BTreeSet<BorrowIndex>>,
}

impl<'tcx> Kills<'_, 'tcx> {
    /// Records the borrows on the specified place as `killed`. For example, when assigning to a
    /// local, or on a call's return destination.
    fn record_killed_borrows_for_place(&mut self, place: Place<'tcx>, location: Location) {
        let other_borrows_of_local = self
            .borrow_set
            .local_map
            .get(&place.local)
            .into_iter()
            .flat_map(|bs| bs.iter())
            .copied();

        // If the borrowed place is a local with no projections, all other borrows of this
        // local must conflict. This is purely an optimization so we don't have to call
        // `places_conflict` for every borrow.
        if place.projection.is_empty() {
            if !self.body.local_decls[place.local].is_ref_to_static() {
                self.kills.entry(location).or_default().extend(other_borrows_of_local);
            }
            return;
        }

        // By passing `PlaceConflictBias::NoOverlap`, we conservatively assume that any given
        // pair of array indices are not equal, so that when `places_conflict` returns true, we
        // will be assured that two places being compared definitely denotes the same sets of
        // locations.
        let definitely_conflicting_borrows = other_borrows_of_local.filter(|&i| {
            places_conflict(
                self.tcx,
                self.body,
                self.borrow_set[i].borrowed_place,
                place,
                PlaceConflictBias::NoOverlap,
            )
        });

        self.kills.entry(location).or_default().extend(definitely_conflicting_borrows);
    }

    /// Records the borrows on the specified local as `killed`.
    fn record_killed_borrows_for_local(&mut self, local: Local, location: Location) {
        if let Some(borrow_indices) = self.borrow_set.local_map.get(&local) {
            self.kills.entry(location).or_default().extend(borrow_indices.iter());
        }
    }
}

impl<'tcx> Visitor<'tcx> for Kills<'_, 'tcx> {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        // If there are borrows on this now dead local, we need to record them as `killed`.
        if let StatementKind::StorageDead(local) = statement.kind {
            self.record_killed_borrows_for_local(local, location);
        }

        self.super_statement(statement, location);
    }

    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        // When we see `X = ...`, then kill borrows of
        // `(*X).foo` and so forth.
        self.record_killed_borrows_for_place(*place, location);
        self.super_assign(place, rvalue, location);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        // A `Call` terminator's return value can be a local which has borrows,
        // so we need to record those as `killed` as well.
        if let TerminatorKind::Call { destination, .. } = terminator.kind {
            self.record_killed_borrows_for_place(destination, location);
        }

        self.super_terminator(terminator, location);
    }
}
