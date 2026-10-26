import LeanComputationalGeometry.Polygon.EarRegion
import LeanComputationalGeometry.Examples.Ears

/-!
# The region of an ear

The unit square and the L-shaped hexagon wind `0` or `1` times off their
boundaries, so the ear theorems apply with no further assumption: the ear
triangles lie in the regions, the regions split along the ears, and the
smaller polygons' open regions miss the ears' interiors.

Traversed clockwise, the L-shaped hexagon is still simple and still has an
ear in the sense of `IsEar` at its inner corner, but that ear triangle is the
notch, outside the polygon: the orientation assumption hidden in
`WindsZeroOrOne` cannot be dropped.
-/

namespace ComputationalGeometry.Examples

open ComputationalGeometry Point2D

noncomputable section

/-! ## The unit square -/

theorem square_windsZeroOrOne : square.WindsZeroOrOne := by
  intro p _
  rw [square_windingNumber,
    edgeContribution_of_horizontal (p := p) (a := mk 0 0) (b := mk 1 0) (by simp),
    edgeContribution_of_horizontal (p := p) (a := mk 1 1) (b := mk 0 1) (by simp)]
  rcases lt_or_ge p.y 0 with h₀ | h₀
  · rw [edgeContribution_of_above (p := p) (a := mk 1 0) (b := mk 1 1) (by simp; linarith)
        (by simp; linarith),
      edgeContribution_of_above (p := p) (a := mk 0 1) (b := mk 0 0) (by simp; linarith)
        (by simp; linarith)]
    simp
  rcases lt_or_ge p.y 1 with h₁ | h₁
  · rw [edgeContribution_of_up (p := p) (a := mk 1 0) (b := mk 1 1) (by simp; linarith)
        (by simp; linarith),
      edgeContribution_of_down (p := p) (a := mk 0 1) (b := mk 0 0) (by simp; linarith)
        (by simp; linarith)]
    simp only [orient_def, x_mk, y_mk]
    norm_num
    split_ifs <;> first | (left; norm_num; done) | (right; norm_num; done) | (exfalso; linarith)
  · rw [edgeContribution_of_below (p := p) (a := mk 1 0) (b := mk 1 1) (by simp; linarith)
        (by simp; linarith),
      edgeContribution_of_below (p := p) (a := mk 0 1) (b := mk 0 0) (by simp; linarith)
        (by simp; linarith)]
    simp

/-- The ear triangle at corner `0` lies in the square's region... -/
example : (square.earTriangle 0).toSet ⊆ square.region :=
  square_isEar_zero.earTriangle_subset_region square_isSimple le_rfl square_windsZeroOrOne

/-- ...the region is the triangle left over together with the ear... -/
example : square.region = (square.removeEar 0).region ∪ (square.earTriangle 0).toSet :=
  square_isEar_zero.region_removeEar square_isSimple le_rfl square_windsZeroOrOne

/-- ...and the two do not overlap inside. -/
example : Disjoint (square.removeEar 0).openRegion (interior (square.earTriangle 0).toSet) :=
  square_isEar_zero.disjoint_openRegion_removeEar square_isSimple le_rfl square_windsZeroOrOne

/-- The triangle left over again winds `0` or `1` times. -/
example : (square.removeEar 0).WindsZeroOrOne :=
  square_isEar_zero.windsZeroOrOne_removeEar square_isSimple le_rfl square_windsZeroOrOne

/-! ## The L-shaped hexagon -/

theorem ell_windsZeroOrOne : ell.WindsZeroOrOne := by
  intro p _
  rw [ell_windingNumber,
    edgeContribution_of_horizontal (p := p) (a := mk 0 0) (b := mk 2 0) (by simp),
    edgeContribution_of_horizontal (p := p) (a := mk 2 1) (b := mk 1 1) (by simp),
    edgeContribution_of_horizontal (p := p) (a := mk 1 2) (b := mk 0 2) (by simp)]
  rcases lt_or_ge p.y 0 with h₀ | h₀
  · rw [edgeContribution_of_above (p := p) (a := mk 2 0) (b := mk 2 1) (by simp; linarith)
        (by simp; linarith),
      edgeContribution_of_above (p := p) (a := mk 1 1) (b := mk 1 2) (by simp; linarith)
        (by simp; linarith),
      edgeContribution_of_above (p := p) (a := mk 0 2) (b := mk 0 0) (by simp; linarith)
        (by simp; linarith)]
    simp
  rcases lt_or_ge p.y 1 with h₁ | h₁
  · rw [edgeContribution_of_up (p := p) (a := mk 2 0) (b := mk 2 1) (by simp; linarith)
        (by simp; linarith),
      edgeContribution_of_above (p := p) (a := mk 1 1) (b := mk 1 2) (by simp; linarith)
        (by simp; linarith),
      edgeContribution_of_down (p := p) (a := mk 0 2) (b := mk 0 0) (by simp; linarith)
        (by simp; linarith)]
    simp only [orient_def, x_mk, y_mk]
    norm_num
    split_ifs <;> first | (left; norm_num; done) | (right; norm_num; done) | (exfalso; linarith)
  rcases lt_or_ge p.y 2 with h₂ | h₂
  · rw [edgeContribution_of_below (p := p) (a := mk 2 0) (b := mk 2 1) (by simp; linarith)
        (by simp; linarith),
      edgeContribution_of_up (p := p) (a := mk 1 1) (b := mk 1 2) (by simp; linarith)
        (by simp; linarith),
      edgeContribution_of_down (p := p) (a := mk 0 2) (b := mk 0 0) (by simp; linarith)
        (by simp; linarith)]
    simp only [orient_def, x_mk, y_mk]
    norm_num
    split_ifs <;> first | (left; norm_num; done) | (right; norm_num; done) | (exfalso; linarith)
  · rw [edgeContribution_of_below (p := p) (a := mk 2 0) (b := mk 2 1) (by simp; linarith)
        (by simp; linarith),
      edgeContribution_of_below (p := p) (a := mk 1 1) (b := mk 1 2) (by simp; linarith)
        (by simp; linarith),
      edgeContribution_of_below (p := p) (a := mk 0 2) (b := mk 0 0) (by simp; linarith)
        (by simp; linarith)]
    simp

/-- The ear at the corner `(2, 0)` lies in the L... -/
example : (ell.earTriangle 1).toSet ⊆ ell.region :=
  ell_isEar_one.earTriangle_subset_region ell_isSimple (by show 4 ≤ 6; norm_num)
    ell_windsZeroOrOne

/-- ...and the L is the pentagon left over together with the ear. -/
example : ell.region = (ell.removeEar 1).region ∪ (ell.earTriangle 1).toSet :=
  ell_isEar_one.region_removeEar ell_isSimple (by show 4 ≤ 6; norm_num) ell_windsZeroOrOne

example : Disjoint (ell.removeEar 1).openRegion (interior (ell.earTriangle 1).toSet) :=
  ell_isEar_one.disjoint_openRegion_removeEar ell_isSimple (by show 4 ≤ 6; norm_num)
    ell_windsZeroOrOne

/-! ## The L, clockwise -/

/-- The L-shaped hexagon traversed clockwise. -/
abbrev ellCW : RawPolygon :=
  ⟨6, ![mk 0 2, mk 1 2, mk 1 1, mk 2 1, mk 2 0, mk 0 0]⟩

theorem ellCW_isSimple : ellCW.IsSimple := by
  refine ⟨by show 3 ≤ 6; norm_num, fun i => ?_, fun i => ?_, fun i j hij h₁ h₂ => ?_⟩
  · change Fin 6 at i
    fin_cases i <;>
      simp [RawPolygon.edge, RawPolygon.next, Segment.Nondegenerate, ellCW, ext_iff']
  · change Fin 6 at i
    fin_cases i <;> simp only [RawPolygon.edge, RawPolygon.next, Segment.toSet, ellCW] <;>
      simp <;> exact Triangle.segment_inter_segment_eq (by norm_num [orient_def])
  · change Fin 6 at i j
    change finRotate 6 i ≠ j at h₁
    change finRotate 6 j ≠ i at h₂
    fin_cases i <;> fin_cases j <;> simp at hij h₁ h₂ <;>
      simp only [RawPolygon.edge, RawPolygon.next, Segment.toSet, ellCW] <;> simp <;>
      exact disjoint_segment_of_coords fun x e₁ x₁ y₁ e₂ x₂ y₂ => by
        simp only [Set.mem_uIcc, x_mk, y_mk] at x₁ y₁ x₂ y₂
        norm_num [orient_def] at e₁ e₂
        rcases x₁ with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases y₁ with ⟨_, _⟩ | ⟨_, _⟩ <;>
          rcases x₂ with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases y₂ with ⟨_, _⟩ | ⟨_, _⟩ <;>
          linarith

theorem ellCW_prev_two : ellCW.prev 2 = 1 := by
  show (finRotate 6).symm 2 = 1
  rw [Equiv.symm_apply_eq]
  decide

theorem ellCW_earTriangle_two : ellCW.earTriangle 2 = ⟨mk 1 2, mk 1 1, mk 2 1⟩ := by
  simp [RawPolygon.earTriangle, RawPolygon.prevVertex, RawPolygon.nextVertex, ellCW_prev_two,
    RawPolygon.next, ellCW]

/-- The inner corner turns left when the L is traversed clockwise, and no other
vertex is in its ear triangle: it passes the ear test. -/
theorem ellCW_isEar_two : ellCW.IsEar 2 := by
  have hT : (ellCW.earTriangle 2).IsCCW := by
    rw [ellCW_earTriangle_two]
    norm_num [Triangle.IsCCW, Triangle.signedArea2, orient_def]
  refine ⟨hT, fun j h₁ h₂ h₃ => ?_⟩
  rw [ellCW_prev_two] at h₁
  change j ≠ finRotate 6 2 at h₃
  rw [finRotate_six_two] at h₃
  rw [Triangle.mem_toSet_iff_containsTest hT, ellCW_earTriangle_two]
  change Fin 6 at j
  fin_cases j
  · rintro ⟨h, -, -⟩; norm_num [ellCW, orient_def] at h
  · exact absurd rfl h₁
  · exact absurd rfl h₂
  · exact absurd rfl h₃
  · rintro ⟨-, h, -⟩; norm_num [ellCW, orient_def] at h
  · rintro ⟨h, -, -⟩; norm_num [ellCW, orient_def] at h

theorem ellCW_windingNumber (p : Point2D) :
    ellCW.windingNumber p = edgeContribution p (mk 0 2) (mk 1 2) +
      edgeContribution p (mk 1 2) (mk 1 1) + edgeContribution p (mk 1 1) (mk 2 1) +
      edgeContribution p (mk 2 1) (mk 2 0) + edgeContribution p (mk 2 0) (mk 0 0) +
      edgeContribution p (mk 0 0) (mk 0 2) := by
  show ∑ i : Fin 6, edgeContribution p (![mk 0 2, mk 1 2, mk 1 1, mk 2 1, mk 2 0, mk 0 0] i)
    (![mk 0 2, mk 1 2, mk 1 1, mk 2 1, mk 2 0, mk 0 0] (finRotate 6 i)) = _
  rw [Fin.sum_univ_six]
  simp

/-- But that ear triangle is the notch, outside the polygon: its centroid is
on no edge and has winding number `0`. -/
theorem ellCW_earTriangle_not_subset_region : ¬ (ellCW.earTriangle 2).toSet ⊆ ellCW.region := by
  intro hsub
  have hT : (ellCW.earTriangle 2).IsCCW := ellCW_isEar_two.isCCW
  have hc : mk (4 / 3) (4 / 3) ∈ (ellCW.earTriangle 2).toSet := by
    rw [Triangle.mem_toSet_iff_containsTest hT, ellCW_earTriangle_two]
    refine ⟨?_, ?_, ?_⟩ <;> norm_num [orient_def]
  rcases hsub hc with ⟨i, hi⟩ | hw
  · have key : ∀ j : Fin 6, mk (4 / 3) (4 / 3) ∉
        (⟨![mk 0 2, mk 1 2, mk 1 1, mk 2 1, mk 2 0, mk 0 0] j,
          ![mk 0 2, mk 1 2, mk 1 1, mk 2 1, mk 2 0, mk 0 0] (finRotate 6 j)⟩ : Segment).toSet := by
      intro j
      rw [mem_toSet_iff]
      fin_cases j <;> norm_num [orient_def, Set.mem_uIcc]
    exact key i hi
  · apply hw
    rw [ellCW_windingNumber]
    norm_num [edgeContribution, orient_def]

/-- Clockwise, the L winds `-1` times around its points: it does not wind `0`
or `1` times. -/
theorem ellCW_not_windsZeroOrOne : ¬ ellCW.WindsZeroOrOne := by
  intro hJ
  have hnb : ¬ ellCW.OnBoundary (mk (1 / 2) (1 / 2)) := by
    rintro ⟨i, hi⟩
    have key : ∀ j : Fin 6, mk (1 / 2) (1 / 2) ∉
        (⟨![mk 0 2, mk 1 2, mk 1 1, mk 2 1, mk 2 0, mk 0 0] j,
          ![mk 0 2, mk 1 2, mk 1 1, mk 2 1, mk 2 0, mk 0 0] (finRotate 6 j)⟩ : Segment).toSet := by
      intro j
      rw [mem_toSet_iff]
      fin_cases j <;> norm_num [orient_def, Set.mem_uIcc]
    exact key i hi
  have hw : ellCW.windingNumber (mk (1 / 2) (1 / 2)) = -1 := by
    rw [ellCW_windingNumber]
    norm_num [edgeContribution, orient_def]
  rcases hJ _ hnb with h | h <;> rw [hw] at h <;> norm_num at h

end

end ComputationalGeometry.Examples
