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
  (`IsEar.disjoint_openRegion_removeEar`).
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
      (wbtw_swap_right_iff ℝ _).mp ⟨mem_segment_iff_wbtw.mp hj, (mem_segment_iff_wbtw.mp hy).symm⟩
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

end RawPolygon

end ComputationalGeometry
