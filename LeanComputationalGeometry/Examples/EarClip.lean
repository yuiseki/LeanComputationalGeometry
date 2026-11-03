import LeanComputationalGeometry.Polygon.EarClip
import LeanComputationalGeometry.Examples.TwoEars

/-!
# Ear clipping

`earClip` on concrete polygons. The general theorems give the number of
triangles, their total signed area and that they cover the region without
overlapping; the polygons need only be simple and counterclockwise.

- the unit square: two triangles of total signed area `2`;
- the comb: seven triangles, covering its region without overlapping;
- the clockwise L: not counterclockwise, so ear clipping applies to it after
  `SimplePolygon.orientCCW`, which keeps its region;
- a ring of four collinear points: no vertex turns left, so there is no ear,
  and `earClip` stops at once with no triangles.
-/

namespace ComputationalGeometry.Examples

open ComputationalGeometry Point2D

noncomputable section

/-! ## The unit square -/

theorem square_length_earClip : square.earClip.length = 2 :=
  square_isSimple.length_earClip square_windsZeroOrOne

example : (square.earClip.map Triangle.signedArea2).sum = 2 := by
  rw [square_isSimple.sum_signedArea2_earClip square_windsZeroOrOne, square_signedArea2]

/-! ## The comb -/

theorem comb_windsZeroOrOne : comb.WindsZeroOrOne := comb_isSimple.windsZeroOrOne_of_isCCW comb_isCCW

theorem comb_length_earClip : comb.earClip.length = 7 :=
  comb_isSimple.length_earClip comb_windsZeroOrOne

example (p : Point2D) : p ∈ comb.region ↔ ∃ T ∈ comb.earClip, p ∈ T.toSet :=
  comb_isSimple.mem_region_iff_earClip comb_windsZeroOrOne

example : comb.earClip.Pairwise (fun T T' => Disjoint (interior T.toSet) (interior T'.toSet)) :=
  comb_isSimple.pairwise_disjoint_earClip comb_windsZeroOrOne

/-- The converse direction: winding `0` or `1` times already makes it
counterclockwise. -/
example : comb.IsCCW := comb_isSimple.isCCW_of_windsZeroOrOne comb_windsZeroOrOne

/-! ## The clockwise L -/

/-- Not counterclockwise, so it does not wind `0` or `1` times. -/
example : ¬ ellCW.WindsZeroOrOne := fun hJ =>
  absurd (ellCW_isSimple.isCCW_of_windsZeroOrOne hJ) (not_lt.mpr ellCW_isCW.le)

/-- The clockwise L as a simple polygon. -/
def ellCWs : SimplePolygon := ⟨ellCW, ellCW_isSimple⟩

theorem ellCW_orientCCW : ellCWs.orientCCW = ellCWs.reverse := by
  unfold SimplePolygon.orientCCW
  split_ifs with h
  · exact absurd h (not_lt.mpr ellCW_isCW.le)
  · rfl

/-- Reversed, it is cut into four triangles covering its region. -/
example : ellCWs.orientCCW.earClip.length = 4 := by
  rw [SimplePolygon.length_earClip _ ellCWs.windsZeroOrOne_orientCCW, ellCW_orientCCW]
  rfl

example (p : Point2D) : p ∈ ellCW.region ↔ ∃ T ∈ ellCWs.orientCCW.earClip, p ∈ T.toSet :=
  ellCWs.mem_toRegion_iff_earClip_orientCCW

/-! ## A flat ring -/

abbrev flat : RawPolygon := ⟨4, ![mk 0 0, mk 1 0, mk 2 0, mk 3 0]⟩

/-- No vertex of four collinear points turns left, so there is no ear and
`earClip` returns nothing: it terminates on every ring. -/
theorem flat_earClip : flat.earClip = [] := by
  have hne : ¬ ∃ i, flat.IsEar i := by
    rintro ⟨i, hi⟩
    have := hi.convexVertex
    have hy : ∀ j, (flat.vertex j).y = 0 := by intro j; fin_cases j <;> rfl
    simp only [RawPolygon.ConvexVertex, RawPolygon.prevVertex, RawPolygon.nextVertex, orient_def,
      hy] at this
    simp at this
  rw [RawPolygon.earClip, dite_eq_right_of_eq_false (eq_false fun h => hne h.2),
    dite_eq_right_of_eq_false (eq_false (by simp))]

end

end ComputationalGeometry.Examples
