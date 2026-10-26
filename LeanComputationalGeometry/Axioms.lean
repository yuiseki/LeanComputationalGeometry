import LeanComputationalGeometry
import LeanComputationalGeometry.Examples.Basic
import LeanComputationalGeometry.Examples.Polygons
import LeanComputationalGeometry.Examples.Ears
import LeanComputationalGeometry.Examples.EarRegion
import LeanComputationalGeometry.Examples.TwoEars

/-!
# Axiom audit

Each theorem below may depend only on Lean's three standard axioms,
`propext`, `Classical.choice` and `Quot.sound`, which come in through
Mathlib's construction of the real numbers. If anything in this project adds
an `axiom` or leaves a proof unfinished (which shows up as `sorryAx`), the
expected messages stop matching and `lake build` fails.

This file is not imported by `LeanComputationalGeometry`; the library's glob
builds it.
-/

/-- info: 'ComputationalGeometry.orient_eq_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.orient_eq_det

/-- info: 'ComputationalGeometry.orient_eq_cross_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.orient_eq_cross_sum

/-- info: 'ComputationalGeometry.orient_swap₁₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.orient_swap₁₂

/-- info: 'ComputationalGeometry.orient_swap₂₃' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.orient_swap₂₃

/-- info: 'ComputationalGeometry.orient_swap₁₃' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.orient_swap₁₃

/-- info: 'ComputationalGeometry.orient_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.orient_rotate

/-- info: 'ComputationalGeometry.orient_add_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.orient_add_vec

/-- info: 'ComputationalGeometry.orient_lineMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.orient_lineMap

/-- info: 'ComputationalGeometry.orient_eq_zero_iff_collinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.orient_eq_zero_iff_collinear

/-- info: 'ComputationalGeometry.orient_ne_zero_iff_affineIndependent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.orient_ne_zero_iff_affineIndependent

/-- info: 'ComputationalGeometry.Segment.orient_eq_zero_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Segment.orient_eq_zero_of_mem

/-- info: 'ComputationalGeometry.mem_toSet_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.mem_toSet_iff

/-- info: 'ComputationalGeometry.properlyIntersect_iff_crossTest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.properlyIntersect_iff_crossTest

/-- info: 'ComputationalGeometry.intersects_iff_crossTest_of_generalPosition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.intersects_iff_crossTest_of_generalPosition

/-- info: 'ComputationalGeometry.intersects_iff_intersectTest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.intersects_iff_intersectTest

/-- info: 'ComputationalGeometry.Triangle.signedArea2_eq_cross_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.signedArea2_eq_cross_sum

/-- info: 'ComputationalGeometry.Triangle.orient_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.orient_sum

/-- info: 'ComputationalGeometry.Triangle.orient_smul_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.orient_smul_sum

/-- info: 'ComputationalGeometry.Triangle.mem_toSet_iff_containsTest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.mem_toSet_iff_containsTest

/-- info: 'ComputationalGeometry.Triangle.nondegenerate_iff_affineIndependent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.nondegenerate_iff_affineIndependent

/-- info: 'ComputationalGeometry.Triangle.segment_inter_segment_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.segment_inter_segment_eq

/-- info: 'ComputationalGeometry.Triangle.isSimple_toPolygon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.isSimple_toPolygon

/-- info: 'ComputationalGeometry.RawPolygon.signedArea2_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.signedArea2_translate

/-- info: 'ComputationalGeometry.RawPolygon.signedArea2_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.signedArea2_rotate

/-- info: 'ComputationalGeometry.Triangle.signedArea2_toPolygon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.signedArea2_toPolygon

/-- info: 'ComputationalGeometry.Examples.diagonals_properlyIntersect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.diagonals_properlyIntersect

/-- info: 'ComputationalGeometry.Examples.parallel_not_intersects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.parallel_not_intersects

/-- info: 'ComputationalGeometry.Examples.square_signedArea2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.square_signedArea2

/-- info: 'ComputationalGeometry.RawPolygon.reverse_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.reverse_edge

/-- info: 'ComputationalGeometry.RawPolygon.signedArea2_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.signedArea2_reverse

/-- info: 'ComputationalGeometry.RawPolygon.isCCW_reverse_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.isCCW_reverse_iff

/-- info: 'ComputationalGeometry.Triangle.mem_segment_iff_of_isCCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.mem_segment_iff_of_isCCW

/-- info: 'ComputationalGeometry.Triangle.mem_interior_toSet_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.mem_interior_toSet_iff

/-- info: 'ComputationalGeometry.Triangle.mem_frontier_toSet_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.mem_frontier_toSet_iff

/-- info: 'ComputationalGeometry.Triangle.mem_frontier_toSet_iff_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.mem_frontier_toSet_iff_edges

/-- info: 'ComputationalGeometry.edgeContribution_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.edgeContribution_swap

/-- info: 'ComputationalGeometry.edgeContribution_of_horizontal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.edgeContribution_of_horizontal

/-- info: 'ComputationalGeometry.edgeContribution_of_orient_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.edgeContribution_of_orient_eq_zero

/-- info: 'ComputationalGeometry.RawPolygon.windingNumber_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.windingNumber_rotate

/-- info: 'ComputationalGeometry.RawPolygon.windingNumber_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.windingNumber_reverse

/-- info: 'ComputationalGeometry.RawPolygon.windingNumber_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.windingNumber_translate

/-- info: 'ComputationalGeometry.RawPolygon.windingNumber_eq_zero_of_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.windingNumber_eq_zero_of_right

/-- info: 'ComputationalGeometry.RawPolygon.region_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.region_reverse

/-- info: 'ComputationalGeometry.RawPolygon.region_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.region_rotate

/-- info: 'ComputationalGeometry.RawPolygon.not_mem_region_of_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.not_mem_region_of_right

/-- info: 'ComputationalGeometry.Triangle.winding3_ne_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.winding3_ne_zero_iff

/-- info: 'ComputationalGeometry.Triangle.mem_region_toPolygon_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.mem_region_toPolygon_iff

/-- info: 'ComputationalGeometry.Triangle.mem_toRegion_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.mem_toRegion_iff

/-- info: 'ComputationalGeometry.Triangle.mem_toOpenRegion_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.mem_toOpenRegion_iff

/-- info: 'ComputationalGeometry.Triangle.toRegion_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.toRegion_eq

/-- info: 'ComputationalGeometry.Examples.ell_windingNumber_notch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.ell_windingNumber_notch

/-- info: 'ComputationalGeometry.Examples.square_windingNumber_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.square_windingNumber_inside

/-- info: 'ComputationalGeometry.Triangle.exists_onEdge_mem_segment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.exists_onEdge_mem_segment

/-- info: 'ComputationalGeometry.Triangle.disjoint_toSet_of_avoid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.disjoint_toSet_of_avoid

/-- info: 'ComputationalGeometry.Triangle.segment_inter_segment_eq_of_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.segment_inter_segment_eq_of_not_mem

/-- info: 'ComputationalGeometry.RawPolygon.distinct5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.distinct5

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.vertex_mem_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.vertex_mem_edge

/-- info: 'ComputationalGeometry.RawPolygon.not_isEar_of_reflexVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.not_isEar_of_reflexVertex

/-- info: 'ComputationalGeometry.RawPolygon.not_isEar_of_locallyDegenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.not_isEar_of_locallyDegenerate

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.disjoint_edge_earDiagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.disjoint_edge_earDiagonal

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.edge_prev_prev_inter_earDiagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.edge_prev_prev_inter_earDiagonal

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.earDiagonal_inter_edge_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.earDiagonal_inter_edge_next

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.earDiagonal_relInterior_inter_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.earDiagonal_relInterior_inter_boundary

/-- info: 'ComputationalGeometry.RawPolygon.Relabel.isSimple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.Relabel.isSimple

/-- info: 'ComputationalGeometry.RawPolygon.Relabel.region_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.Relabel.region_eq

/-- info: 'ComputationalGeometry.RawPolygon.removeEar_n' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.removeEar_n

/-- info: 'ComputationalGeometry.RawPolygon.sum_edges_removeEar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.sum_edges_removeEar

/-- info: 'ComputationalGeometry.RawPolygon.signedArea2_removeEar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.signedArea2_removeEar

/-- info: 'ComputationalGeometry.RawPolygon.windingNumber_removeEar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.windingNumber_removeEar

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.isSimple_removeEar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.isSimple_removeEar

/-- info: 'ComputationalGeometry.RawPolygon.region_removeEar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.region_removeEar

/-- info: 'ComputationalGeometry.SimplePolygon.toRegion_removeEar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.SimplePolygon.toRegion_removeEar

/-- info: 'ComputationalGeometry.Examples.square_isSimple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.square_isSimple

/-- info: 'ComputationalGeometry.Examples.square_isEar_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.square_isEar_zero

/-- info: 'ComputationalGeometry.Examples.square_removeEar_isSimple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.square_removeEar_isSimple

/-- info: 'ComputationalGeometry.Examples.ell_not_isEar_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.ell_not_isEar_zero

/-- info: 'ComputationalGeometry.Examples.ell_isEar_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.ell_isEar_one

/-- info: 'ComputationalGeometry.Examples.square_isEar_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.square_isEar_two

/-- info: 'ComputationalGeometry.Examples.ell_isSimple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.ell_isSimple

/-- info: 'ComputationalGeometry.Examples.ell_removeEar_isSimple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.ell_removeEar_isSimple

/-- info: 'ComputationalGeometry.mem_segment_of_orient_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.mem_segment_of_orient_eq_zero

/-- info: 'ComputationalGeometry.edgeContribution_eventually_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.edgeContribution_eventually_eq

/-- info: 'ComputationalGeometry.RawPolygon.sum_sub_next_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.sum_sub_next_mul

/-- info: 'ComputationalGeometry.RawPolygon.windingNumber_eventually_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.windingNumber_eventually_eq

/-- info: 'ComputationalGeometry.RawPolygon.continuousAt_windingNumber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.continuousAt_windingNumber

/-- info: 'ComputationalGeometry.RawPolygon.windingNumber_eq_of_isPreconnected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.windingNumber_eq_of_isPreconnected

/-- info: 'ComputationalGeometry.RawPolygon.isClosed_onBoundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.isClosed_onBoundary

/-- info: 'ComputationalGeometry.RawPolygon.isOpen_openRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.isOpen_openRegion

/-- info: 'ComputationalGeometry.RawPolygon.isClosed_region' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.isClosed_region

/-- info: 'ComputationalGeometry.RawPolygon.windingNumber_eventually_eq_add_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.windingNumber_eventually_eq_add_edge

/-- info: 'ComputationalGeometry.SimplePolygon.isOpen_toOpenRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.SimplePolygon.isOpen_toOpenRegion

/-- info: 'ComputationalGeometry.Triangle.winding3_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.winding3_eq_one

/-- info: 'ComputationalGeometry.Triangle.isPreconnected_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.isPreconnected_interior

/-- info: 'ComputationalGeometry.Triangle.closure_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.closure_interior

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.disjoint_edge_earTriangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.disjoint_edge_earTriangle

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.not_onBoundary_of_mem_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.not_onBoundary_of_mem_interior

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.not_mem_edge_of_mem_openSegment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.not_mem_edge_of_mem_openSegment

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.exists_sides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.exists_sides

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.exists_sides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.exists_sides

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.windingNumber_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.windingNumber_eq_one

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.interior_earTriangle_subset_openRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.interior_earTriangle_subset_openRegion

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.earTriangle_subset_region' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.earTriangle_subset_region

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.earDiagonal_subset_region' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.earDiagonal_subset_region

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.region_removeEar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.region_removeEar

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.disjoint_openRegion_removeEar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.disjoint_openRegion_removeEar

/-- info: 'ComputationalGeometry.SimplePolygon.toRegion_eq_removeEar_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.SimplePolygon.toRegion_eq_removeEar_union

/-- info: 'ComputationalGeometry.SimplePolygon.disjoint_toOpenRegion_removeEar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.SimplePolygon.disjoint_toOpenRegion_removeEar

/-- info: 'ComputationalGeometry.Examples.square_windsZeroOrOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.square_windsZeroOrOne

/-- info: 'ComputationalGeometry.Examples.ell_windsZeroOrOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.ell_windsZeroOrOne

/-- info: 'ComputationalGeometry.Examples.ellCW_isSimple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.ellCW_isSimple

/-- info: 'ComputationalGeometry.Examples.ellCW_isEar_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.ellCW_isEar_two

/-- info: 'ComputationalGeometry.Examples.ellCW_earTriangle_not_subset_region' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.ellCW_earTriangle_not_subset_region

/-- info: 'ComputationalGeometry.Examples.ellCW_not_windsZeroOrOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.ellCW_not_windsZeroOrOne

/-- info: 'ComputationalGeometry.RawPolygon.onBoundary_removeEar_or' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.onBoundary_removeEar_or

/-- info: 'ComputationalGeometry.Triangle.winding3_eq_zero_of_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Triangle.winding3_eq_zero_of_not_mem

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.windsZeroOrOne_removeEar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.windsZeroOrOne_removeEar

/-- info: 'ComputationalGeometry.SimplePolygon.windsZeroOrOne_removeEar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.SimplePolygon.windsZeroOrOne_removeEar

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.reverse

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.not_forall_orient_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.not_forall_orient_eq_zero

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.exists_edge_y_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.exists_edge_y_ne

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.exists_orient_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.exists_orient_ne_zero

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.dot_pos_of_locallyDegenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.dot_pos_of_locallyDegenerate

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.eventually_leftSector_not_onBoundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.eventually_leftSector_not_onBoundary

/-- info: 'ComputationalGeometry.RawPolygon.isPreconnected_leftSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.isPreconnected_leftSector

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.eventually_thinLeft_not_onBoundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.eventually_thinLeft_not_onBoundary

/-- info: 'ComputationalGeometry.RawPolygon.eventually_mem_thinLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.eventually_mem_thinLeft

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.eventually_thinLeft_meets_leftSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.eventually_thinLeft_meets_leftSector

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.eventually_thinLeft_meets_leftSector_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.eventually_thinLeft_meets_leftSector_next

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.exists_left_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.exists_left_value

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.exists_approach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.exists_approach

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.exists_sides₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.exists_sides₂

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.windingNumber_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.windingNumber_cases

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.abs_windingNumber_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.abs_windingNumber_le_one

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.windsZeroOrOne_of_isCCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.windsZeroOrOne_of_isCCW

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.windingNumber_eq_zero_or_neg_one_of_isCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.windingNumber_eq_zero_or_neg_one_of_isCW

/-- info: 'ComputationalGeometry.RawPolygon.WindsZeroOrOne.signedArea2_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.WindsZeroOrOne.signedArea2_nonneg

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.earTriangle_subset_region_of_isCCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.earTriangle_subset_region_of_isCCW

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.interior_earTriangle_subset_openRegion_of_isCCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.interior_earTriangle_subset_openRegion_of_isCCW

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.region_removeEar_of_isCCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.region_removeEar_of_isCCW

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.disjoint_openRegion_removeEar_of_isCCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.disjoint_openRegion_removeEar_of_isCCW

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.windsZeroOrOne_removeEar_of_isCCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.windsZeroOrOne_removeEar_of_isCCW

/-- info: 'ComputationalGeometry.SimplePolygon.windsZeroOrOne_of_isCCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.SimplePolygon.windsZeroOrOne_of_isCCW

/-- info: 'ComputationalGeometry.SimplePolygon.toRegion_eq_removeEar_union_of_isCCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.SimplePolygon.toRegion_eq_removeEar_union_of_isCCW

/-- info: 'ComputationalGeometry.SimplePolygon.disjoint_toOpenRegion_removeEar_of_isCCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.SimplePolygon.disjoint_toOpenRegion_removeEar_of_isCCW

/-- info: 'ComputationalGeometry.edgeContribution_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.edgeContribution_mk

/-- info: 'ComputationalGeometry.integral_edgeContribution_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.integral_edgeContribution_mk

/-- info: 'ComputationalGeometry.integral_crossSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.integral_crossSign

/-- info: 'ComputationalGeometry.RawPolygon.signedArea2_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.signedArea2_eq_integral

/-- info: 'ComputationalGeometry.RawPolygon.signedArea2_nonneg_of_windingNumber_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.signedArea2_nonneg_of_windingNumber_nonneg

/-- info: 'ComputationalGeometry.Examples.square_isCCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.square_isCCW

/-- info: 'ComputationalGeometry.Examples.ell_isCCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.ell_isCCW

/-- info: 'ComputationalGeometry.Examples.ellCW_isCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.ellCW_isCW

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.exists_side_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.exists_side_values

/-- info: 'ComputationalGeometry.RawPolygon.iterate_next_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.iterate_next_inj

/-- info: 'ComputationalGeometry.RawPolygon.exists_iterate_next_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.exists_iterate_next_eq

/-- info: 'ComputationalGeometry.RawPolygon.sum_range_iterate_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.sum_range_iterate_next

/-- info: 'ComputationalGeometry.RawPolygon.windingNumber_chain_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.windingNumber_chain_add

/-- info: 'ComputationalGeometry.RawPolygon.onBoundary_chain_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.onBoundary_chain_iff

/-- info: 'ComputationalGeometry.RawPolygon.onBoundary_chain_or' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.onBoundary_chain_or

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.vertex_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.vertex_injective

/-- info: 'ComputationalGeometry.RawPolygon.IsDiagonal.symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsDiagonal.symm

/-- info: 'ComputationalGeometry.RawPolygon.IsDiagonal.eq_or_eq_of_onBoundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsDiagonal.eq_or_eq_of_onBoundary

/-- info: 'ComputationalGeometry.RawPolygon.IsDiagonal.mem_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsDiagonal.mem_edge

/-- info: 'ComputationalGeometry.RawPolygon.IsDiagonal.isSimple_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsDiagonal.isSimple_chain

/-- info: 'ComputationalGeometry.RawPolygon.exists_left_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.exists_left_near

/-- info: 'ComputationalGeometry.RawPolygon.IsDiagonal.windsZeroOrOne_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsDiagonal.windsZeroOrOne_chain

/-- info: 'ComputationalGeometry.RawPolygon.IsDiagonal.openRegion_chain_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsDiagonal.openRegion_chain_subset

/-- info: 'ComputationalGeometry.RawPolygon.IsDiagonal.disjoint_openRegion_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsDiagonal.disjoint_openRegion_chain

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.exists_convexVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.exists_convexVertex

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.eq_of_mem_edge_inter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.eq_of_mem_edge_inter

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.openSegment_subset_openRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.openSegment_subset_openRegion

/-- info: 'ComputationalGeometry.RawPolygon.IsEar.isDiagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsEar.isDiagonal

/-- info: 'ComputationalGeometry.RawPolygon.ConvexVertex.exists_isDiagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.ConvexVertex.exists_isDiagonal

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.exists_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.exists_diagonal

/-- info: 'ComputationalGeometry.RawPolygon.chain_two_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.chain_two_eq

/-- info: 'ComputationalGeometry.RawPolygon.IsDiagonal.isEar_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsDiagonal.isEar_two

/-- info: 'ComputationalGeometry.RawPolygon.IsDiagonal.exists_ear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsDiagonal.exists_ear

/-- info: 'ComputationalGeometry.RawPolygon.isEar_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.isEar_chain

/-- info: 'ComputationalGeometry.RawPolygon.IsDiagonal.interior_earTriangle_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsDiagonal.interior_earTriangle_subset

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.exists_ear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.exists_ear

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.exists_two_nonoverlapping_ears' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.exists_two_nonoverlapping_ears

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.exists_two_ears' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.exists_two_ears

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.exists_ear_of_isCCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.exists_ear_of_isCCW

/-- info: 'ComputationalGeometry.RawPolygon.IsSimple.exists_two_nonoverlapping_ears_of_isCCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.RawPolygon.IsSimple.exists_two_nonoverlapping_ears_of_isCCW

/-- info: 'ComputationalGeometry.SimplePolygon.exists_ear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.SimplePolygon.exists_ear

/-- info: 'ComputationalGeometry.SimplePolygon.isEar_someEar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.SimplePolygon.isEar_someEar

/-- info: 'ComputationalGeometry.SimplePolygon.exists_ear_of_isCCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.SimplePolygon.exists_ear_of_isCCW

/-- info: 'ComputationalGeometry.SimplePolygon.exists_two_nonoverlapping_ears' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.SimplePolygon.exists_two_nonoverlapping_ears

/-- info: 'ComputationalGeometry.SimplePolygon.exists_two_nonoverlapping_ears_of_isCCW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.SimplePolygon.exists_two_nonoverlapping_ears_of_isCCW

/-- info: 'ComputationalGeometry.Examples.pentagon_isSimple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.pentagon_isSimple

/-- info: 'ComputationalGeometry.Examples.squareMid_isSimple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.squareMid_isSimple

/-- info: 'ComputationalGeometry.Examples.comb_isSimple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.comb_isSimple

/-- info: 'ComputationalGeometry.Examples.comb_isEar_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.comb_isEar_two

/-- info: 'ComputationalGeometry.Examples.comb_isEar_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputationalGeometry.Examples.comb_isEar_six
