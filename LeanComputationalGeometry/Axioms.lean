import LeanComputationalGeometry
import LeanComputationalGeometry.Examples.Basic

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
