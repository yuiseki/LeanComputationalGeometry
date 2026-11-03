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

/-- Off its boundary, the smaller ring winds `0` times around the points of the
ear triangle: inside, `1 - 1 = 0`, and on its sides by local constancy. -/
theorem IsEar.windingNumber_removeEar_eq_zero (hP : P.IsSimple) (h4 : 4 ≤ P.n) {i : Fin P.n}
    (h : P.IsEar i) (hJ : P.WindsZeroOrOne) {p : Point2D} (hpT : p ∈ (P.earTriangle i).toSet)
    (hpQ : ¬ (P.removeEar i).OnBoundary p) : (P.removeEar i).windingNumber p = 0 := by
  have hcl : p ∈ closure (interior (P.earTriangle i).toSet) := by
    rw [Triangle.closure_interior h.isCCW]; exact hpT
  obtain ⟨q, hqT, hq⟩ := ((mem_closure_iff_frequently.mp hcl).and_eventually
    ((P.removeEar i).windingNumber_eventually_eq hpQ)).exists
  have h₁ := windingNumber_removeEar P (by omega) i q
  rw [h.windingNumber_eq_one hP h4 hJ hqT,
    Triangle.winding3_eq_one h.isCCW ((Triangle.mem_interior_toSet_iff h.isCCW q).mp hqT)] at h₁
  rw [← hq]
  omega

/-- The smaller ring's open region lies in the polygon's. -/
theorem IsEar.openRegion_removeEar_subset (hP : P.IsSimple) (h4 : 4 ≤ P.n) {i : Fin P.n}
    (h : P.IsEar i) (hJ : P.WindsZeroOrOne) : (P.removeEar i).openRegion ⊆ P.openRegion := by
  rintro p ⟨hpQ, hw⟩
  have hpT : p ∉ (P.earTriangle i).toSet := fun hpT =>
    hw (h.windingNumber_removeEar_eq_zero hP h4 hJ hpT hpQ)
  refine ⟨fun hb => (onBoundary_removeEar_or (by omega) i hb).elim hpQ hpT, ?_⟩
  rw [windingNumber_removeEar P (by omega) i, Triangle.winding3_eq_zero_of_not_mem h.isCCW hpT,
    add_zero]
  exact hw

/-- Ear clipping runs down to a triangle: `n - 2` counterclockwise triangles
whose signed areas add up to the polygon's, which cover the polygon's closed
region and whose interiors lie in its open region and do not overlap. -/
theorem IsSimple.earClip_spec :
    ∀ (m : ℕ) {P : RawPolygon}, P.n = m → P.IsSimple → P.WindsZeroOrOne →
      P.earClip.length = P.n - 2 ∧ (∀ T ∈ P.earClip, T.IsCCW) ∧
        (P.earClip.map Triangle.signedArea2).sum = P.signedArea2 ∧
        (∀ p, p ∈ P.region ↔ ∃ T ∈ P.earClip, p ∈ T.toSet) ∧
        (∀ T ∈ P.earClip, interior T.toSet ⊆ P.openRegion) ∧
        P.earClip.Pairwise (fun T T' => Disjoint (interior T.toSet) (interior T'.toSet)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro P hm hP hJ
  have h3 := hP.three_le
  rcases h3.eq_or_lt with h3 | h4
  · have hT := hP.isCCW_earTriangle_of_n_eq_three hJ h3.symm
    have hPT := eq_earTriangle_toPolygon h3.symm
    rw [earClip_of_n_eq_three h3.symm]
    refine ⟨by simp; omega, by simpa using hT, ?_, fun p => ?_, ?_, by simp⟩
    · conv_rhs => rw [hPT]
      simp [Triangle.signedArea2_toPolygon]
    · conv_lhs => rw [hPT]
      simp [Triangle.mem_region_toPolygon_iff_of_isCCW hT]
    · simp only [List.mem_singleton, forall_eq]
      intro p hp
      rw [hPT]
      exact (Triangle.mem_openRegion_toPolygon_iff_of_isCCW hT).mpr hp
  obtain ⟨i, hi, he⟩ := exists_earClip_eq_cons h4 (hP.exists_ear hJ h4)
  have hQn := removeEar_n P i
  obtain ⟨hl, hc, hs, hr, ho, hd⟩ := ih _ (by omega) rfl (hi.isSimple_removeEar hP h4)
    (hi.windsZeroOrOne_removeEar hP h4 hJ)
  rw [he]
  refine ⟨by simp [hl]; omega, ?_, ?_, fun p => ?_, ?_, ?_⟩
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨hi.isCCW, hc⟩
  · rw [List.map_cons, List.sum_cons, hs, signedArea2_removeEar P (by omega) i]
    ring
  · rw [hi.region_removeEar hP h4 hJ, mem_union, hr]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_comm
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨hi.interior_earTriangle_subset_openRegion hP h4 hJ,
      fun T hT => (ho T hT).trans (hi.openRegion_removeEar_subset hP h4 hJ)⟩
  · refine List.Pairwise.cons (fun T hT => ?_) hd
    exact ((hi.disjoint_openRegion_removeEar hP h4 hJ).mono_left (ho T hT)).symm

theorem IsSimple.length_earClip (hP : P.IsSimple) (hJ : P.WindsZeroOrOne) :
    P.earClip.length = P.n - 2 :=
  (IsSimple.earClip_spec _ rfl hP hJ).1

theorem IsSimple.isCCW_of_mem_earClip (hP : P.IsSimple) (hJ : P.WindsZeroOrOne) {T : Triangle}
    (hT : T ∈ P.earClip) : T.IsCCW :=
  (IsSimple.earClip_spec _ rfl hP hJ).2.1 T hT

theorem IsSimple.sum_signedArea2_earClip (hP : P.IsSimple) (hJ : P.WindsZeroOrOne) :
    (P.earClip.map Triangle.signedArea2).sum = P.signedArea2 :=
  (IsSimple.earClip_spec _ rfl hP hJ).2.2.1

/-- The triangles cover the polygon's closed region. -/
theorem IsSimple.mem_region_iff_earClip (hP : P.IsSimple) (hJ : P.WindsZeroOrOne) {p : Point2D} :
    p ∈ P.region ↔ ∃ T ∈ P.earClip, p ∈ T.toSet :=
  (IsSimple.earClip_spec _ rfl hP hJ).2.2.2.1 p

theorem IsSimple.interior_subset_openRegion_of_mem_earClip (hP : P.IsSimple)
    (hJ : P.WindsZeroOrOne) {T : Triangle} (hT : T ∈ P.earClip) :
    interior T.toSet ⊆ P.openRegion :=
  (IsSimple.earClip_spec _ rfl hP hJ).2.2.2.2.1 T hT

/-- The triangles do not overlap. -/
theorem IsSimple.pairwise_disjoint_earClip (hP : P.IsSimple) (hJ : P.WindsZeroOrOne) :
    P.earClip.Pairwise (fun T T' => Disjoint (interior T.toSet) (interior T'.toSet)) :=
  (IsSimple.earClip_spec _ rfl hP hJ).2.2.2.2.2

/-! ## Orientation -/

/-- A simple polygon that winds `0` or `1` times is counterclockwise: its
signed area is a sum of at least one positive triangle area. -/
theorem IsSimple.isCCW_of_windsZeroOrOne (hP : P.IsSimple) (hJ : P.WindsZeroOrOne) : P.IsCCW := by
  have hl := hP.length_earClip hJ
  have h3 := hP.three_le
  show 0 < P.signedArea2
  rw [← hP.sum_signedArea2_earClip hJ]
  refine List.sum_pos _ (fun x hx => ?_) (by simp; intro e; simp [e] at hl; omega)
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hx
  exact hP.isCCW_of_mem_earClip hJ hT

theorem IsSimple.isCCW_iff_windsZeroOrOne (hP : P.IsSimple) : P.IsCCW ↔ P.WindsZeroOrOne :=
  ⟨hP.windsZeroOrOne_of_isCCW, hP.isCCW_of_windsZeroOrOne⟩

/-- A simple polygon is counterclockwise or clockwise. -/
theorem IsSimple.isCCW_or_isCW (hP : P.IsSimple) : P.IsCCW ∨ P.IsCW := by
  rcases hP.windingNumber_cases with h | h
  · exact Or.inl (hP.isCCW_of_windsZeroOrOne h)
  · refine Or.inr ((isCCW_reverse_iff P).mp (hP.reverse.isCCW_of_windsZeroOrOne fun p hp => ?_))
    rw [windingNumber_reverse]
    rcases h p ((onBoundary_reverse P p).not.mp hp) with e | e <;> omega

/-- A simple polygon has a nonzero shoelace sum. -/
theorem IsSimple.signedArea2_ne_zero (hP : P.IsSimple) : P.signedArea2 ≠ 0 := by
  rcases hP.isCCW_or_isCW with h | h
  · exact ne_of_gt h
  · exact ne_of_lt h

end RawPolygon

end ComputationalGeometry
