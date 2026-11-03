import LeanComputationalGeometry.Polygon.TwoEars

/-!
# Ear clipping

`earClip P` cuts ears off `P` one after another, by recursion on the number of
vertices: with four vertices or more it cuts off some ear, chosen without a
policy, and goes on with the smaller ring; with three it returns the triangle
itself. The recursion is total and terminates on every ring, since cutting an
ear drops one vertex (`removeEar_n`); when a ring with four vertices or more
has no ear, it stops with no triangles.

For a simple polygon that winds `0` or `1` times there is always an ear
(`IsSimple.exists_ear`), and cutting it keeps both properties
(`IsEar.isSimple_removeEar`, `IsEar.windsZeroOrOne_removeEar`), so the
recursion runs down to a triangle. Then:

- `length_earClip`: there are `n - 2` triangles;
- `isCCW_of_mem_earClip`: each is counterclockwise;
- `sum_signedArea2_earClip`: their signed areas add up to the polygon's.
-/

namespace ComputationalGeometry

open Set Point2D

namespace RawPolygon

variable {P : RawPolygon}

open Classical in
/-- Cut ears off a ring until a triangle is left, with no assumption on the
ring. -/
noncomputable def earClip (P : RawPolygon) : List Triangle :=
  if h : 4 ≤ P.n ∧ ∃ i, P.IsEar i then
    P.earTriangle h.2.choose :: (P.removeEar h.2.choose).earClip
  else if h3 : P.n = 3 then [P.earTriangle ⟨1, by omega⟩]
  else []
termination_by P.n
decreasing_by rw [removeEar_n]; omega

/-- With four vertices or more and an ear, `earClip` cuts some ear. -/
theorem exists_earClip_eq_cons (h4 : 4 ≤ P.n) (he : ∃ i, P.IsEar i) :
    ∃ i, P.IsEar i ∧ P.earClip = P.earTriangle i :: (P.removeEar i).earClip := by
  refine ⟨he.choose, he.choose_spec, ?_⟩
  rw [earClip, dite_eq_left_of_eq_true (eq_true ⟨h4, he⟩)]

theorem earClip_of_n_eq_three (h3 : P.n = 3) : P.earClip = [P.earTriangle ⟨1, by omega⟩] := by
  rw [earClip, dite_eq_right_of_eq_false (eq_false (by omega)), dite_eq_left_of_eq_true (eq_true h3)]

/-- A ring of three vertices is the ear triangle of its middle vertex. -/
theorem eq_earTriangle_toPolygon (h3 : P.n = 3) : P = (P.earTriangle ⟨1, by omega⟩).toPolygon := by
  obtain ⟨n, v⟩ := P
  simp only at h3
  subst h3
  unfold Triangle.toPolygon
  congr 1
  funext m
  fin_cases m <;> rfl

/-- A simple ring of three vertices that winds `0` or `1` times is a
counterclockwise triangle. -/
theorem IsSimple.isCCW_earTriangle_of_n_eq_three (hP : P.IsSimple) (hJ : P.WindsZeroOrOne)
    (h3 : P.n = 3) : (P.earTriangle ⟨1, by omega⟩).IsCCW := by
  set T := P.earTriangle ⟨1, by omega⟩
  have hPT : P = T.toPolygon := eq_earTriangle_toPolygon h3
  have hnd : T.signedArea2 ≠ 0 := by
    have hab : T.a ≠ T.b := fun e => prev_ne_self hP.three_le _ (hP.vertex_injective e)
    rw [hPT] at hP
    obtain ⟨m, hm⟩ := not_forall.mp (hP.not_forall_orient_eq_zero hab)
    fin_cases m
    · exact (hm (by show orient T.a T.b T.a = 0; simp)).elim
    · exact (hm (by show orient T.a T.b T.b = 0; simp)).elim
    · exact hm
  have hpos : 0 ≤ T.signedArea2 := by
    have := hJ.signedArea2_nonneg
    rwa [hPT, Triangle.signedArea2_toPolygon] at this
  exact lt_of_le_of_ne hpos (Ne.symm hnd)

/-- Ear clipping runs down to a triangle: `n - 2` counterclockwise triangles
whose signed areas add up to the polygon's. -/
theorem IsSimple.earClip_spec :
    ∀ (m : ℕ) {P : RawPolygon}, P.n = m → P.IsSimple → P.WindsZeroOrOne →
      P.earClip.length = P.n - 2 ∧ (∀ T ∈ P.earClip, T.IsCCW) ∧
        (P.earClip.map Triangle.signedArea2).sum = P.signedArea2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro P hm hP hJ
  have h3 := hP.three_le
  rcases h3.eq_or_lt with h3 | h4
  · have hT := hP.isCCW_earTriangle_of_n_eq_three hJ h3.symm
    rw [earClip_of_n_eq_three h3.symm]
    refine ⟨by simp; omega, by simpa using hT, ?_⟩
    conv_rhs => rw [eq_earTriangle_toPolygon h3.symm]
    simp [Triangle.signedArea2_toPolygon]
  obtain ⟨i, hi, he⟩ := exists_earClip_eq_cons h4 (hP.exists_ear hJ h4)
  have hQn := removeEar_n P i
  obtain ⟨hl, hc, hs⟩ := ih _ (by omega) rfl (hi.isSimple_removeEar hP h4)
    (hi.windsZeroOrOne_removeEar hP h4 hJ)
  rw [he]
  refine ⟨by simp [hl]; omega, ?_, ?_⟩
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨hi.isCCW, hc⟩
  · rw [List.map_cons, List.sum_cons, hs, signedArea2_removeEar P (by omega) i]
    ring

theorem IsSimple.length_earClip (hP : P.IsSimple) (hJ : P.WindsZeroOrOne) :
    P.earClip.length = P.n - 2 :=
  (IsSimple.earClip_spec _ rfl hP hJ).1

theorem IsSimple.isCCW_of_mem_earClip (hP : P.IsSimple) (hJ : P.WindsZeroOrOne) {T : Triangle}
    (hT : T ∈ P.earClip) : T.IsCCW :=
  (IsSimple.earClip_spec _ rfl hP hJ).2.1 T hT

theorem IsSimple.sum_signedArea2_earClip (hP : P.IsSimple) (hJ : P.WindsZeroOrOne) :
    (P.earClip.map Triangle.signedArea2).sum = P.signedArea2 :=
  (IsSimple.earClip_spec _ rfl hP hJ).2.2

end RawPolygon

end ComputationalGeometry
