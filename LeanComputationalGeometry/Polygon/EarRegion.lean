import LeanComputationalGeometry.Polygon.RemoveEar
import LeanComputationalGeometry.Polygon.WindingTopology
import Mathlib.Analysis.Convex.Between

/-!
# The region of an ear

For an ear of a simple polygon with at least four vertices:

1. the interior of the ear triangle avoids the boundary
   (`IsEar.not_onBoundary_of_mem_interior`): edges away from the ear miss the
   closed triangle, the ear's own edges are sides of it, and the edges just
   before and after it reach it only at the diagonal's ends;
2. the interior is convex, hence preconnected, so the winding number is
   constant on it (`RawPolygon.windingNumber_eq_of_isPreconnected`);
3. just across one of the ear's own edges, from outside the triangle to
   inside, the winding number goes up by one (`IsSimple.exists_sides`, from
   `RawPolygon.windingNumber_eventually_eq_add_edge`).

What 3 does not say is whether the value inside is `1` (the triangle is in
the polygon) or `0` (it is outside). Nothing local can say it: traversed
clockwise, the L-shaped hexagon has an ear in the notch, outside the polygon
(`Examples.ellCW_isEar_two`). For a counterclockwise simple polygon the
Jordan curve theorem gives it, in this form: off the boundary the polygon
winds `0` or `1` times (`WindsZeroOrOne`). That is the one global fact the
theorems below assume. With it, the winding number is `1` on the interior of
the ear triangle (`IsEar.windingNumber_eq_one`), so

- the interior of the ear triangle is in the open region and the closed ear
  triangle in the closed region (`IsEar.interior_earTriangle_subset_openRegion`,
  `IsEar.earTriangle_subset_region`);
- the region splits along the ear with no further assumption
  (`IsEar.region_removeEar`);
- the smaller polygon's open region misses the interior of the ear triangle,
  where its winding number is `1 - 1 = 0`
  (`IsEar.disjoint_openRegion_removeEar`);
- the smaller polygon again winds `0` or `1` times
  (`IsEar.windsZeroOrOne_removeEar`), so ears can be cut one after another.
-/

namespace ComputationalGeometry

open Set Point2D Filter Topology

namespace Triangle

variable {T : Triangle}

theorem isPreconnected_interior (T : Triangle) : IsPreconnected (interior T.toSet) :=
  (convex_convexHull ℝ _).interior.isPreconnected

/-- A counterclockwise triangle has interior points: the centroid. -/
theorem interior_nonempty (h : T.IsCCW) : (interior T.toSet).Nonempty := by
  have hA : 0 < orient T.a T.b T.c := h
  refine ⟨(1 / 3 : ℝ) • T.a + (1 / 3 : ℝ) • T.b + (1 / 3 : ℝ) • T.c,
    (mem_interior_toSet_iff h _).mpr ⟨?_, ?_, ?_⟩⟩ <;>
  · simp only [orient_def, x_add, x_smul, y_add, y_smul] at hA ⊢
    nlinarith

theorem closure_interior (h : T.IsCCW) : closure (interior T.toSet) = T.toSet := by
  show closure (interior (convexHull ℝ {T.a, T.b, T.c})) = T.toSet
  rw [Convex.closure_interior_eq_closure_of_nonempty_interior (convex_convexHull ℝ _)
    (interior_nonempty h)]
  exact (isClosed_toSet h).closure_eq

end Triangle

namespace RawPolygon

variable {P : RawPolygon}

/-- Off the boundary the ring winds `0` or `1` times. For a counterclockwise
simple polygon this is what the Jordan curve theorem says about winding
numbers; it is not proved here. -/
def WindsZeroOrOne (P : RawPolygon) : Prop :=
  ∀ p, ¬ P.OnBoundary p → P.windingNumber p = 0 ∨ P.windingNumber p = 1

/-! ## The interior of an ear triangle avoids the boundary -/

theorem IsEar.not_onBoundary_of_mem_interior (hP : P.IsSimple) (h4 : 4 ≤ P.n) {i : Fin P.n}
    (h : P.IsEar i) {x : Point2D} (hx : x ∈ interior (P.earTriangle i).toSet) :
    ¬ P.OnBoundary x := by
  have hT := h.isCCW
  have hs := (Triangle.mem_interior_toSet_iff hT x).mp hx
  have hxT := interior_subset hx
  have hd := P.distinct5 h4 i
  rintro ⟨j, hj⟩
  rw [edge_toSet] at hj
  by_cases e₁ : j = P.prev (P.prev i)
  · subst e₁
    rw [next_prev] at hj
    -- Leaving the triangle towards the far end of the edge, the segment reaches
    -- the triangle's boundary, which it can meet only at `prevVertex i`.
    obtain ⟨y, hy, hyc, hyz⟩ := Triangle.exists_onEdge_mem_segment hT hxT
      (h.empty _ hd.pp_ne_prev hd.pp_ne hd.pp_ne_next)
    have hyE : y ∈ segment ℝ (P.vertex (P.prev (P.prev i))) (P.vertex (P.prev i)) :=
      (convex_segment _ _).segment_subset hj (left_mem_segment ℝ _ _) hy
    have hyA : y = P.prevVertex i := by
      rcases Triangle.mem_edges_of_onEdge hT hyc hyz with h₁ | h₁ | h₁
      · have hadj := hP.adjacent_inter (P.prev (P.prev i))
        simp only [next_prev, edge_toSet] at hadj
        exact hadj.subset ⟨hyE, h₁⟩
      · have hdis := hP.nonadjacent_disjoint (P.prev (P.prev i)) i hd.pp_ne
          (by rw [next_prev]; exact hd.prev_ne) (Ne.symm hd.pp_ne_next)
        simp only [next_prev, edge_toSet] at hdis
        exact absurd h₁ (Set.disjoint_left.mp hdis hyE)
      · have := (h.edge_prev_prev_inter_earDiagonal hP h4).subset
          (⟨by rw [edge_toSet, next_prev]; exact hyE,
            by rw [Segment.toSet, earDiagonal, segment_symm]; exact h₁⟩ :
            y ∈ (P.edge (P.prev (P.prev i))).toSet ∩ (P.earDiagonal i).toSet)
        exact this
    rw [hyA] at hy
    have hxA : x = P.prevVertex i :=
      (wbtw_swap_right_iff ℝ _).mp
        ⟨mem_segment_iff_wbtw.mp hj, (mem_segment_iff_wbtw.mp hy).symm⟩
    have := hs.2.2
    rw [hxA] at this
    simp [earTriangle] at this
  by_cases e₂ : j = P.prev i
  · subst e₂
    rw [next_prev] at hj
    exact hs.1.ne' (Segment.orient_eq_zero_of_mem ⟨_, _⟩ hj)
  by_cases e₃ : j = i
  · subst e₃
    exact hs.2.1.ne' (Segment.orient_eq_zero_of_mem ⟨_, _⟩ hj)
  by_cases e₄ : j = P.next i
  · subst e₄
    obtain ⟨y, hy, hyc, hyz⟩ := Triangle.exists_onEdge_mem_segment hT hxT
      (h.empty _ hd.nn_ne_prev hd.nn_ne hd.nn_ne_next)
    have hyE : y ∈ segment ℝ (P.vertex (P.next i)) (P.vertex (P.next (P.next i))) :=
      (convex_segment _ _).segment_subset hj (right_mem_segment ℝ _ _) hy
    have hyC : y = P.nextVertex i := by
      rcases Triangle.mem_edges_of_onEdge hT hyc hyz with h₁ | h₁ | h₁
      · have hdis := hP.nonadjacent_disjoint (P.next i) (P.prev i) (Ne.symm hd.prev_ne_next)
          hd.nn_ne_prev (by rw [next_prev]; exact Ne.symm hd.next_ne)
        simp only [next_prev, edge_toSet] at hdis
        exact absurd h₁ (Set.disjoint_left.mp hdis hyE)
      · have hadj := hP.adjacent_inter i
        simp only [edge_toSet] at hadj
        exact hadj.subset ⟨h₁, hyE⟩
      · exact (h.earDiagonal_inter_edge_next hP h4).subset
          (⟨by rw [Segment.toSet, earDiagonal, segment_symm]; exact h₁,
            by rw [edge_toSet]; exact hyE⟩ :
            y ∈ (P.earDiagonal i).toSet ∩ (P.edge (P.next i)).toSet)
    rw [hyC] at hy
    have hxC : x = P.nextVertex i :=
      (wbtw_swap_right_iff ℝ _).mp
        ⟨(mem_segment_iff_wbtw.mp hj).symm, (mem_segment_iff_wbtw.mp hy).symm⟩
    have := hs.2.1
    rw [hxC] at this
    simp [earTriangle] at this
  exact Set.disjoint_left.mp (h.disjoint_edge_earTriangle hP e₁ e₂ e₃ e₄)
    (by rw [edge_toSet]; exact hj) hxT

/-! ## Across an edge of a simple polygon -/

/-- A point inside an edge of a simple polygon is on no other edge. -/
theorem IsSimple.not_mem_edge_of_mem_openSegment (hP : P.IsSimple) {e k : Fin P.n} (hk : k ≠ e)
    {p : Point2D} (hp : p ∈ openSegment ℝ (P.vertex e) (P.vertex (P.next e))) :
    p ∉ segment ℝ (P.vertex k) (P.vertex (P.next k)) := by
  intro hpk
  have hpe : p ∈ segment ℝ (P.vertex e) (P.vertex (P.next e)) :=
    openSegment_subset_segment _ _ _ hp
  have hne : P.vertex e ≠ P.vertex (P.next e) := hP.edge_nondegenerate e
  by_cases h₁ : k = P.next e
  · subst h₁
    have := (hP.adjacent_inter e).subset ⟨hpe, hpk⟩
    rw [mem_singleton_iff] at this
    rw [this] at hp
    exact hne (right_mem_openSegment_iff.mp hp)
  by_cases h₂ : P.next k = e
  · have hk' : k = P.prev e := by rw [← h₂, prev_next]
    subst hk'
    have := (hP.adjacent_inter (P.prev e)).subset ⟨hpk, by rw [next_prev]; exact hpe⟩
    rw [mem_singleton_iff, next_prev] at this
    rw [this] at hp
    exact hne (left_mem_openSegment_iff.mp hp)
  exact Set.disjoint_left.mp (hP.nonadjacent_disjoint k e hk h₂ (Ne.symm h₁)) hpk hpe

/-- Next to the middle of a non-horizontal edge of a simple polygon there are
points off the boundary on both sides, and the winding number on the left is
one more than on the right. The points can be taken in any sets `S` and `S'`
containing all points near the middle on the left and on the right. -/
theorem IsSimple.exists_sides₂ (hP : P.IsSimple) (e : Fin P.n) {u w : Point2D}
    (hu : P.vertex e = u) (hw : P.vertex (P.next e) = w) (hy : u.y ≠ w.y) {S S' : Set Point2D}
    (hS : ∀ᶠ q in 𝓝 ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • w), 0 < orient u w q → q ∈ S)
    (hS' : ∀ᶠ q in 𝓝 ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • w), orient u w q < 0 → q ∈ S') :
    ∃ q q', q ∈ S ∧ q' ∈ S' ∧ ¬ P.OnBoundary q ∧ ¬ P.OnBoundary q' ∧
      P.windingNumber q = P.windingNumber q' + 1 := by
  subst hu hw
  set m : Point2D := (1 / 2 : ℝ) • P.vertex e + (1 / 2 : ℝ) • P.vertex (P.next e) with hmdef
  have hm : m ∈ openSegment ℝ (P.vertex e) (P.vertex (P.next e)) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hoff : ∀ k, k ≠ e → m ∉ segment ℝ (P.vertex k) (P.vertex (P.next k)) :=
    fun k hk => hP.not_mem_edge_of_mem_openSegment hk hm
  have hmy : m.y = ((P.vertex e).y + (P.vertex (P.next e)).y) / 2 := by
    simp only [hmdef, y_add, y_smul]; ring
  have hum : (P.vertex e).y ≠ m.y := by rw [hmy]; intro h; apply hy; linarith
  have hwm : (P.vertex (P.next e)).y ≠ m.y := by rw [hmy]; intro h; apply hy; linarith
  obtain ⟨K, hK⟩ := P.windingNumber_eventually_eq_add_edge e hoff hum hwm
  -- Off the edge's line, its contribution is `1` on the left and `0` on the right, up to a
  -- constant.
  obtain ⟨d, hd⟩ : ∃ d : ℤ, ∀ᶠ q in 𝓝 m, orient (P.vertex e) (P.vertex (P.next e)) q ≠ 0 →
      edgeContribution q (P.vertex e) (P.vertex (P.next e)) =
        (if 0 < orient (P.vertex e) (P.vertex (P.next e)) q then 1 else 0) + d := by
    rcases lt_or_gt_of_ne hy with hlt | hgt
    · refine ⟨0, ?_⟩
      filter_upwards [eventually_y_gt (show (P.vertex e).y < m.y by rw [hmy]; linarith),
        eventually_y_lt (show m.y < (P.vertex (P.next e)).y by rw [hmy]; linarith)] with q h₁ h₂ _
      rw [edgeContribution_of_up h₁.le h₂, add_zero]
    · refine ⟨-1, ?_⟩
      filter_upwards [eventually_y_lt (show m.y < (P.vertex e).y by rw [hmy]; linarith),
        eventually_y_gt (show (P.vertex (P.next e)).y < m.y by rw [hmy]; linarith)]
        with q h₁ h₂ h₀
      rw [edgeContribution_of_down h₁ h₂.le]
      rcases lt_or_gt_of_ne h₀ with hn | hn
      · simp [hn, not_lt.mpr hn.le]
      · simp [hn, not_lt.mpr hn.le]
  have hedges :
      ∀ᶠ q in 𝓝 m, ∀ k, k ≠ e → q ∉ segment ℝ (P.vertex k) (P.vertex (P.next k)) := by
    refine eventually_all.mpr fun k => ?_
    by_cases hk : k = e
    · exact Eventually.of_forall fun q h => absurd hk h
    · exact Filter.mem_of_superset ((isClosed_segment _ _).isOpen_compl.mem_nhds (hoff k hk))
        fun q hq _ => hq
  have hE := hK.and (hd.and (hedges.and (hS.and hS')))
  -- Walk away from the middle along the normal.
  set nrm : Point2D := Point2D.mk (-((P.vertex (P.next e)).y - (P.vertex e).y))
    ((P.vertex (P.next e)).x - (P.vertex e).x) with hnrm
  set L := ((P.vertex (P.next e)).x - (P.vertex e).x) ^ 2 +
    ((P.vertex (P.next e)).y - (P.vertex e).y) ^ 2 with hL
  have horient : ∀ t : ℝ, orient (P.vertex e) (P.vertex (P.next e)) (m + t • nrm) = t * L := by
    intro t
    simp only [hmdef, hnrm, hL, orient_def, x_add, y_add, x_smul, y_smul, Point2D.x_mk, Point2D.y_mk]
    ring
  have hLpos : 0 < L := by
    have : 0 < ((P.vertex (P.next e)).y - (P.vertex e).y) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hy.symm)))
    rw [hL]; nlinarith [sq_nonneg ((P.vertex (P.next e)).x - (P.vertex e).x)]
  have hγ : Tendsto (fun t : ℝ => m + t • nrm) (𝓝 0) (𝓝 m) := by
    have : Continuous fun t : ℝ => m + t • nrm := by fun_prop
    simpa using this.tendsto 0
  have hEt := hγ.eventually hE
  obtain ⟨t, htE, ht⟩ := ((hEt.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  obtain ⟨t', htE', ht'⟩ := ((hEt.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Iio (0 : ℝ) ∈ 𝓝[<] 0)).exists
  have ho : 0 < orient (P.vertex e) (P.vertex (P.next e)) (m + t • nrm) := by
    rw [horient]; exact mul_pos ht hLpos
  have ho' : orient (P.vertex e) (P.vertex (P.next e)) (m + t' • nrm) < 0 := by
    rw [horient]; exact mul_neg_of_neg_of_pos ht' hLpos
  have notOnB : ∀ q, (∀ k, k ≠ e → q ∉ segment ℝ (P.vertex k) (P.vertex (P.next k))) →
      orient (P.vertex e) (P.vertex (P.next e)) q ≠ 0 → ¬ P.OnBoundary q := by
    rintro q hq h₀ ⟨k, hk⟩
    by_cases hke : k = e
    · subst hke
      exact h₀ (Segment.orient_eq_zero_of_mem ⟨_, _⟩ hk)
    · exact hq k hke hk
  refine ⟨_, _, htE.2.2.2.1 ho, htE'.2.2.2.2 ho', notOnB _ htE.2.2.1 ho.ne',
    notOnB _ htE'.2.2.1 ho'.ne, ?_⟩
  rw [htE.1, htE'.1, htE.2.1 ho.ne', htE'.2.1 ho'.ne]
  simp [ho, not_lt.mpr ho'.le]
  ring

/-- Next to the middle of a non-horizontal edge of a simple polygon there are
points off the boundary on both sides, and the winding number on the left is
one more than on the right. The left-hand points can be taken in any set `S`
containing all left-hand points near the middle. -/
theorem IsSimple.exists_sides (hP : P.IsSimple) (e : Fin P.n) {u w : Point2D}
    (hu : P.vertex e = u) (hw : P.vertex (P.next e) = w) (hy : u.y ≠ w.y) {S : Set Point2D}
    (hS : ∀ᶠ q in 𝓝 ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • w), 0 < orient u w q → q ∈ S) :
    ∃ q q', q ∈ S ∧ ¬ P.OnBoundary q ∧ ¬ P.OnBoundary q' ∧
      P.windingNumber q = P.windingNumber q' + 1 := by
  obtain ⟨q, q', hq, -, h₁, h₂, h₃⟩ := hP.exists_sides₂ e hu hw hy (S' := univ) hS
    (Eventually.of_forall fun _ _ => mem_univ _)
  exact ⟨q, q', hq, h₁, h₂, h₃⟩

/-! ## The ear triangle is inside -/

/-- Next to an ear there are points off the boundary on both sides of one of
its two edges, the inner one in the interior of the ear triangle, and the
winding number there is one more than across the edge. -/
theorem IsEar.exists_sides (hP : P.IsSimple) {i : Fin P.n} (h : P.IsEar i) :
    ∃ q q', q ∈ interior (P.earTriangle i).toSet ∧ ¬ P.OnBoundary q ∧ ¬ P.OnBoundary q' ∧
      P.windingNumber q = P.windingNumber q' + 1 := by
  have hT := h.isCCW
  have hA : 0 < orient (P.prevVertex i) (P.vertex i) (P.nextVertex i) := h.convex
  by_cases hAB : (P.prevVertex i).y = (P.vertex i).y
  · -- Across the edge from vertex `i`, which is not horizontal.
    have hBC : (P.vertex i).y ≠ (P.nextVertex i).y := by
      intro hBC
      have : orient (P.prevVertex i) (P.vertex i) (P.nextVertex i) = 0 := by
        rw [orient_def, hAB, hBC]; ring
      exact hA.ne' this
    refine hP.exists_sides i rfl rfl hBC ?_
    set m : Point2D := (1 / 2 : ℝ) • P.vertex i + (1 / 2 : ℝ) • P.nextVertex i
    have h₁ : 0 < orient (P.prevVertex i) (P.vertex i) m := by
      have : orient (P.prevVertex i) (P.vertex i) m =
          orient (P.prevVertex i) (P.vertex i) (P.nextVertex i) / 2 := by
        simp only [m, orient_def, x_add, x_smul, y_add, y_smul]; ring
      rw [this]; linarith
    have h₃ : 0 < orient (P.nextVertex i) (P.prevVertex i) m := by
      have : orient (P.nextVertex i) (P.prevVertex i) m =
          orient (P.prevVertex i) (P.vertex i) (P.nextVertex i) / 2 := by
        simp only [m, orient_def, x_add, x_smul, y_add, y_smul]; ring
      rw [this]; linarith
    filter_upwards [eventually_orient_pos h₁, eventually_orient_pos h₃] with q hq₁ hq₃ hq₂
    exact (Triangle.mem_interior_toSet_iff hT q).mpr ⟨hq₁, hq₂, hq₃⟩
  · -- Across the edge into vertex `i`.
    refine hP.exists_sides (P.prev i) rfl (by rw [next_prev]) hAB ?_
    set m : Point2D := (1 / 2 : ℝ) • P.prevVertex i + (1 / 2 : ℝ) • P.vertex i
    have h₂ : 0 < orient (P.vertex i) (P.nextVertex i) m := by
      have : orient (P.vertex i) (P.nextVertex i) m =
          orient (P.prevVertex i) (P.vertex i) (P.nextVertex i) / 2 := by
        simp only [m, orient_def, x_add, x_smul, y_add, y_smul]; ring
      rw [this]; linarith
    have h₃ : 0 < orient (P.nextVertex i) (P.prevVertex i) m := by
      have : orient (P.nextVertex i) (P.prevVertex i) m =
          orient (P.prevVertex i) (P.vertex i) (P.nextVertex i) / 2 := by
        simp only [m, orient_def, x_add, x_smul, y_add, y_smul]; ring
      rw [this]; linarith
    filter_upwards [eventually_orient_pos h₂, eventually_orient_pos h₃] with q hq₂ hq₃ hq₁
    exact (Triangle.mem_interior_toSet_iff hT q).mpr ⟨hq₁, hq₂, hq₃⟩

/-- On the interior of an ear triangle the winding number is `1`, for a polygon
that winds `0` or `1` times. -/
theorem IsEar.windingNumber_eq_one (hP : P.IsSimple) (h4 : 4 ≤ P.n) {i : Fin P.n}
    (h : P.IsEar i) (hJ : P.WindsZeroOrOne) {x : Point2D}
    (hx : x ∈ interior (P.earTriangle i).toSet) : P.windingNumber x = 1 := by
  obtain ⟨q, q', hqT, hq, hq', hqq⟩ := h.exists_sides hP
  have h₁ : P.windingNumber q = 1 := by
    rcases hJ q hq with e | e <;> rcases hJ q' hq' with e' | e' <;> omega
  rw [← h₁]
  exact P.windingNumber_eq_of_isPreconnected (Triangle.isPreconnected_interior _)
    (fun y hy => h.not_onBoundary_of_mem_interior hP h4 hy) hx hqT

theorem IsEar.interior_earTriangle_subset_openRegion (hP : P.IsSimple) (h4 : 4 ≤ P.n)
    {i : Fin P.n} (h : P.IsEar i) (hJ : P.WindsZeroOrOne) :
    interior (P.earTriangle i).toSet ⊆ P.openRegion := fun x hx =>
  ⟨h.not_onBoundary_of_mem_interior hP h4 hx, by
    rw [h.windingNumber_eq_one hP h4 hJ hx]; exact one_ne_zero⟩

/-- The closed ear triangle lies in the closed region: it is the closure of
its interior, and the region is closed. -/
theorem IsEar.earTriangle_subset_region (hP : P.IsSimple) (h4 : 4 ≤ P.n) {i : Fin P.n}
    (h : P.IsEar i) (hJ : P.WindsZeroOrOne) : (P.earTriangle i).toSet ⊆ P.region := by
  rw [← Triangle.closure_interior h.isCCW, P.isClosed_region.closure_subset_iff]
  exact fun x hx => P.openRegion_subset_region (h.interior_earTriangle_subset_openRegion hP h4 hJ hx)

theorem IsEar.earDiagonal_subset_region (hP : P.IsSimple) (h4 : 4 ≤ P.n) {i : Fin P.n}
    (h : P.IsEar i) (hJ : P.WindsZeroOrOne) : (P.earDiagonal i).toSet ⊆ P.region :=
  (earDiagonal_subset_earTriangle i).trans (h.earTriangle_subset_region hP h4 hJ)

/-- The region splits along an ear, with no assumption on the ear triangle. -/
theorem IsEar.region_removeEar (hP : P.IsSimple) (h4 : 4 ≤ P.n) {i : Fin P.n} (h : P.IsEar i)
    (hJ : P.WindsZeroOrOne) :
    P.region = (P.removeEar i).region ∪ (P.earTriangle i).toSet :=
  RawPolygon.region_removeEar (by omega) h.convex (h.earTriangle_subset_region hP h4 hJ)

/-- The smaller polygon's open region misses the interior of the ear triangle:
there its winding number is `1 - 1 = 0`. -/
theorem IsEar.disjoint_openRegion_removeEar (hP : P.IsSimple) (h4 : 4 ≤ P.n) {i : Fin P.n}
    (h : P.IsEar i) (hJ : P.WindsZeroOrOne) :
    Disjoint (P.removeEar i).openRegion (interior (P.earTriangle i).toSet) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, hw⟩ hx
  have hP1 := h.windingNumber_eq_one hP h4 hJ hx
  have hT1 := Triangle.winding3_eq_one h.isCCW ((Triangle.mem_interior_toSet_iff h.isCCW x).mp hx)
  have := windingNumber_removeEar P (by omega) i x
  rw [hP1, hT1] at this
  exact hw (by omega)

/-- The smaller polygon again winds `0` or `1` times: off the ear triangle its
winding numbers are the polygon's, and on the ear triangle they are `0`, inside
because `1 - 1 = 0` and on its sides by local constancy. So ears can be cut
one after another. -/
theorem IsEar.windsZeroOrOne_removeEar (hP : P.IsSimple) (h4 : 4 ≤ P.n) {i : Fin P.n}
    (h : P.IsEar i) (hJ : P.WindsZeroOrOne) : (P.removeEar i).WindsZeroOrOne := by
  intro p hpQ
  have hdec := windingNumber_removeEar P (by omega) i
  by_cases hpT : p ∈ (P.earTriangle i).toSet
  · left
    have hcl : p ∈ closure (interior (P.earTriangle i).toSet) := by
      rw [Triangle.closure_interior h.isCCW]; exact hpT
    obtain ⟨q, hqT, hq⟩ := ((mem_closure_iff_frequently.mp hcl).and_eventually
      ((P.removeEar i).windingNumber_eventually_eq hpQ)).exists
    have h₁ := hdec q
    rw [h.windingNumber_eq_one hP h4 hJ hqT,
      Triangle.winding3_eq_one h.isCCW ((Triangle.mem_interior_toSet_iff h.isCCW q).mp hqT)] at h₁
    rw [← hq]
    omega
  · have hpP : ¬ P.OnBoundary p := fun hb =>
      (onBoundary_removeEar_or (by omega) i hb).elim hpQ hpT
    have h₁ := hdec p
    rw [Triangle.winding3_eq_zero_of_not_mem h.isCCW hpT, add_zero] at h₁
    rw [← h₁]
    exact hJ p hpP

end RawPolygon

namespace SimplePolygon

theorem earTriangle_subset_toRegion (P : SimplePolygon) (h4 : 4 ≤ P.1.n) {i : Fin P.1.n}
    (h : P.1.IsEar i) (hJ : P.1.WindsZeroOrOne) : (P.1.earTriangle i).toSet ⊆ P.toRegion :=
  h.earTriangle_subset_region P.2 h4 hJ

/-- The region of a simple polygon splits along an ear into the region of the
smaller simple polygon and the ear triangle. -/
theorem toRegion_eq_removeEar_union (P : SimplePolygon) (h4 : 4 ≤ P.1.n) (i : Fin P.1.n)
    (h : P.1.IsEar i) (hJ : P.1.WindsZeroOrOne) :
    P.toRegion = (P.removeEar h4 i h).toRegion ∪ (P.1.earTriangle i).toSet :=
  h.region_removeEar P.2 h4 hJ

theorem windsZeroOrOne_removeEar (P : SimplePolygon) (h4 : 4 ≤ P.1.n) (i : Fin P.1.n)
    (h : P.1.IsEar i) (hJ : P.1.WindsZeroOrOne) : (P.removeEar h4 i h).1.WindsZeroOrOne :=
  h.windsZeroOrOne_removeEar P.2 h4 hJ

theorem disjoint_toOpenRegion_removeEar (P : SimplePolygon) (h4 : 4 ≤ P.1.n) (i : Fin P.1.n)
    (h : P.1.IsEar i) (hJ : P.1.WindsZeroOrOne) :
    Disjoint (P.removeEar h4 i h).toOpenRegion (interior (P.1.earTriangle i).toSet) :=
  h.disjoint_openRegion_removeEar P.2 h4 hJ

end SimplePolygon

end ComputationalGeometry
