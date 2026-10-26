import LeanComputationalGeometry.Polygon.Region
import LeanComputationalGeometry.TriangleCrossing

/-!
# Ears

Vertex `i` of a ring, with its neighbours `prev i` and `next i`, spans the
triangle `earTriangle i`; the segment from `prev i` to `next i` is the
`earDiagonal`. The vertex is convex, reflex or locally degenerate as the
triangle turns counterclockwise, clockwise or not at all.

`IsEar i` is the test ear clipping makes: the vertex is convex and no other
vertex lies in the closed ear triangle. The triangle is taken closed on
purpose. A vertex on the diagonal would let the diagonal touch the boundary,
and cutting the ear would leave a ring that is not simple.

For a simple polygon with at least four vertices the diagonal of an ear meets
the boundary only at its ends (`earDiagonal_relInterior_inter_boundary`):

- edges away from the ear miss the whole triangle
  (`disjoint_edge_earDiagonal`, from `Triangle.disjoint_toSet_of_avoid`);
- the edges just before and after the ear meet the diagonal only at its ends
  (`edge_prev_prev_inter_earDiagonal`, `earDiagonal_inter_edge_next`);
- the ear's own two edges meet it only at its ends, because the triangle is
  nondegenerate.

Whether the ear triangle lies in the region the polygon bounds is a separate
question, not decided here: it needs facts about winding numbers of simple
polygons of the Jordan curve kind (see `Polygon/RemoveEar.lean`).
-/

namespace ComputationalGeometry

open Set Point2D

namespace RawPolygon

variable (P : RawPolygon)

/-! ## Indices around a vertex -/

theorem val_next (j : Fin P.n) : (P.next j).val = (j.val + 1) % P.n := by
  obtain ⟨_ | n, v⟩ := P
  · exact j.elim0
  show (finRotate (n + 1) j).val = _
  rw [finRotate_apply, Fin.val_add]
  simp [Nat.add_mod]

theorem val_iterate_next (j : Fin P.n) (k : ℕ) : (P.next^[k] j).val = (j.val + k) % P.n := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt j.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply', val_next, ih, Nat.mod_add_mod, Nat.add_assoc]

/-- Going `k` steps forward, `0 < k < n`, does not come back. -/
theorem iterate_next_ne (j : Fin P.n) {k : ℕ} (hk0 : 0 < k) (hk : k < P.n) : P.next^[k] j ≠ j := by
  intro h
  have h' := congrArg Fin.val h
  rw [val_iterate_next] at h'
  have hj := j.isLt
  rcases Nat.lt_or_ge (j.val + k) P.n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h'; omega
  · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h'; omega

theorem next_injective : Function.Injective P.next := (finRotate P.n).injective

/-- The five indices around vertex `i` are as distinct as they can be, given
at least four vertices: only `prev (prev i)` and `next (next i)` may agree. -/
structure Distinct5 (i : Fin P.n) : Prop where
  prev_ne : P.prev i ≠ i
  next_ne : P.next i ≠ i
  prev_ne_next : P.prev i ≠ P.next i
  pp_ne_prev : P.prev (P.prev i) ≠ P.prev i
  pp_ne : P.prev (P.prev i) ≠ i
  pp_ne_next : P.prev (P.prev i) ≠ P.next i
  nn_ne_prev : P.next (P.next i) ≠ P.prev i
  nn_ne : P.next (P.next i) ≠ i
  nn_ne_next : P.next (P.next i) ≠ P.next i

theorem distinct5 (h4 : 4 ≤ P.n) (i : Fin P.n) : P.Distinct5 i := by
  -- Everything in terms of `a = prev (prev i)`, from which `i` is two steps on.
  obtain ⟨a, rfl⟩ : ∃ a, i = P.next (P.next a) := ⟨P.prev (P.prev i), by simp⟩
  have ne : ∀ (x : Fin P.n) (k : ℕ), 0 < k → k < P.n → P.next^[k] x ≠ x :=
    fun x k h0 hk => P.iterate_next_ne x h0 hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try simp only [prev_next]
  · exact fun e => ne (P.next a) 1 (by omega) (by omega) e.symm
  · exact ne (P.next (P.next a)) 1 (by omega) (by omega)
  · exact fun e => ne (P.next a) 2 (by omega) (by omega) e.symm
  · exact fun e => ne a 1 (by omega) (by omega) e.symm
  · exact fun e => ne a 2 (by omega) (by omega) e.symm
  · exact fun e => ne a 3 (by omega) (by omega) e.symm
  · exact ne (P.next a) 3 (by omega) (by omega)
  · exact ne (P.next (P.next a)) 2 (by omega) (by omega)
  · exact ne (P.next (P.next (P.next a))) 1 (by omega) (by omega)

/-! ## The ear triangle -/

/-- The vertex before vertex `i`. -/
def prevVertex (i : Fin P.n) : Point2D := P.vertex (P.prev i)

/-- The vertex after vertex `i`. -/
def nextVertex (i : Fin P.n) : Point2D := P.vertex (P.next i)

/-- The triangle of vertex `i` and its two neighbours. -/
def earTriangle (i : Fin P.n) : Triangle := ⟨P.prevVertex i, P.vertex i, P.nextVertex i⟩

/-- The segment joining the two neighbours of vertex `i`. -/
def earDiagonal (i : Fin P.n) : Segment := ⟨P.prevVertex i, P.nextVertex i⟩

/-- The ring turns left at vertex `i`. -/
def ConvexVertex (i : Fin P.n) : Prop :=
  0 < orient (P.prevVertex i) (P.vertex i) (P.nextVertex i)

/-- The ring turns right at vertex `i`. -/
def ReflexVertex (i : Fin P.n) : Prop :=
  orient (P.prevVertex i) (P.vertex i) (P.nextVertex i) < 0

/-- The ring goes straight on, or back, at vertex `i`. -/
def LocallyDegenerate (i : Fin P.n) : Prop :=
  orient (P.prevVertex i) (P.vertex i) (P.nextVertex i) = 0

theorem convex_or_reflex_or_locallyDegenerate (i : Fin P.n) :
    P.ConvexVertex i ∨ P.ReflexVertex i ∨ P.LocallyDegenerate i := by
  rcases lt_trichotomy 0 (orient (P.prevVertex i) (P.vertex i) (P.nextVertex i)) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h.symm)
  · exact Or.inr (Or.inl h)

/-- Vertex `i` is an ear: it is convex, and no other vertex lies in the closed
ear triangle. -/
structure IsEar (i : Fin P.n) : Prop where
  convex : P.ConvexVertex i
  empty : ∀ j, j ≠ P.prev i → j ≠ i → j ≠ P.next i → P.vertex j ∉ (P.earTriangle i).toSet

variable {P}

theorem IsEar.convexVertex {i : Fin P.n} (h : P.IsEar i) : P.ConvexVertex i := h.convex

theorem IsEar.isCCW {i : Fin P.n} (h : P.IsEar i) : (P.earTriangle i).IsCCW := h.convex

theorem not_isEar_of_reflexVertex {i : Fin P.n} (h : P.ReflexVertex i) : ¬ P.IsEar i :=
  fun he => absurd he.convex (not_lt.mpr h.le)

theorem not_isEar_of_locallyDegenerate {i : Fin P.n} (h : P.LocallyDegenerate i) : ¬ P.IsEar i :=
  fun he => absurd he.convex (by rw [ConvexVertex, h]; exact lt_irrefl 0)

theorem earDiagonal_subset_earTriangle (i : Fin P.n) :
    (P.earDiagonal i).toSet ⊆ (P.earTriangle i).toSet := by
  rw [Segment.toSet, segment_symm]
  exact Triangle.segment_subset_toSet (by simp [earTriangle, earDiagonal])
    (by simp [earTriangle, earDiagonal])

theorem IsEar.prevVertex_ne_nextVertex {i : Fin P.n} (h : P.IsEar i) :
    P.prevVertex i ≠ P.nextVertex i := by
  intro e
  have := h.convex
  rw [ConvexVertex, e, orient_self₁₃] at this
  exact lt_irrefl 0 this

/-! ## The diagonal of an ear in a simple polygon -/

/-- In a simple polygon, a vertex lies only on the two edges through it. -/
theorem IsSimple.vertex_mem_edge (hP : P.IsSimple) {j k : Fin P.n}
    (h : P.vertex k ∈ (P.edge j).toSet) : j = k ∨ P.next j = k := by
  by_contra hc
  simp only [not_or] at hc
  by_cases hkj : P.next k = j
  · have hk := hP.adjacent_inter k
    rw [hkj] at hk
    have : P.vertex k ∈ (P.edge k).toSet ∩ (P.edge j).toSet := ⟨(P.edge k).p_mem_toSet, h⟩
    rw [hk, mem_singleton_iff, ← hkj] at this
    exact hP.edge_nondegenerate k this
  · exact Set.disjoint_left.mp (hP.nonadjacent_disjoint j k hc.1 hc.2 hkj) h (P.edge k).p_mem_toSet

theorem edge_toSet (j : Fin P.n) :
    (P.edge j).toSet = segment ℝ (P.vertex j) (P.vertex (P.next j)) := rfl

/-- Edges away from an ear miss its diagonal: they miss the whole ear
triangle. -/
theorem IsEar.disjoint_edge_earDiagonal (hP : P.IsSimple) {i : Fin P.n} (h : P.IsEar i)
    {j : Fin P.n} (h₁ : j ≠ P.prev (P.prev i)) (h₂ : j ≠ P.prev i) (h₃ : j ≠ i)
    (h₄ : j ≠ P.next i) : Disjoint (P.edge j).toSet (P.earDiagonal i).toSet := by
  have hn₁ : P.next j ≠ P.prev i := fun e => h₁ (by rw [← e, prev_next])
  have hn₂ : P.next j ≠ i := fun e => h₂ (by rw [← e, prev_next])
  have hn₃ : P.next j ≠ P.next i := fun e => h₃ (P.next_injective e)
  have hab := hP.nonadjacent_disjoint j (P.prev i) h₂ hn₁ (by rw [next_prev]; exact Ne.symm h₃)
  have hbc := hP.nonadjacent_disjoint j i h₃ hn₂ (Ne.symm h₄)
  rw [edge_toSet, edge_toSet, next_prev] at hab
  rw [edge_toSet, edge_toSet] at hbc
  have key := Triangle.disjoint_toSet_of_avoid h.isCCW (h.empty j h₂ h₃ h₄)
    (h.empty (P.next j) hn₁ hn₂ hn₃) hab hbc
  rw [edge_toSet]
  exact key.mono_right (earDiagonal_subset_earTriangle i)

/-- The edge before an ear meets the diagonal only at its start. -/
theorem IsEar.edge_prev_prev_inter_earDiagonal (hP : P.IsSimple) (h4 : 4 ≤ P.n) {i : Fin P.n}
    (h : P.IsEar i) :
    (P.edge (P.prev (P.prev i))).toSet ∩ (P.earDiagonal i).toSet = {P.prevVertex i} := by
  have hd := P.distinct5 h4 i
  rw [edge_toSet, next_prev]
  apply Triangle.segment_inter_segment_eq_of_not_mem
  · exact fun hm => h.empty _ hd.pp_ne_prev hd.pp_ne hd.pp_ne_next
      (earDiagonal_subset_earTriangle i hm)
  · intro hm
    have hm' : P.vertex (P.next i) ∈ (P.edge (P.prev (P.prev i))).toSet := by
      rw [edge_toSet, next_prev]; exact hm
    rcases hP.vertex_mem_edge hm' with e | e
    · exact hd.pp_ne_next e
    · rw [next_prev] at e; exact hd.prev_ne_next e

/-- The edge after an ear meets the diagonal only at its end. -/
theorem IsEar.earDiagonal_inter_edge_next (hP : P.IsSimple) (h4 : 4 ≤ P.n) {i : Fin P.n}
    (h : P.IsEar i) :
    (P.earDiagonal i).toSet ∩ (P.edge (P.next i)).toSet = {P.nextVertex i} := by
  have hd := P.distinct5 h4 i
  rw [edge_toSet]
  show segment ℝ (P.prevVertex i) (P.nextVertex i) ∩
    segment ℝ (P.nextVertex i) (P.vertex (P.next (P.next i))) = _
  rw [inter_comm, segment_symm ℝ (P.nextVertex i), segment_symm ℝ (P.prevVertex i)]
  apply Triangle.segment_inter_segment_eq_of_not_mem
  · intro hm
    rw [segment_symm] at hm
    exact h.empty _ hd.nn_ne_prev hd.nn_ne hd.nn_ne_next (earDiagonal_subset_earTriangle i hm)
  · intro hm
    rw [segment_symm] at hm
    rcases hP.vertex_mem_edge (j := P.next i) (k := P.prev i) hm with e | e
    · exact hd.prev_ne_next e.symm
    · exact hd.nn_ne_prev e

/-- The diagonal of an ear meets the boundary only at its ends. -/
theorem IsEar.earDiagonal_relInterior_inter_boundary (hP : P.IsSimple) (h4 : 4 ≤ P.n)
    {i : Fin P.n} (h : P.IsEar i) :
    (P.earDiagonal i).relInterior ∩ {p | P.OnBoundary p} = ∅ := by
  have hAC := h.prevVertex_ne_nextVertex
  have hA : P.prevVertex i ∉ (P.earDiagonal i).relInterior := by
    rw [Segment.relInterior, earDiagonal, left_mem_openSegment_iff]; exact hAC
  have hC : P.nextVertex i ∉ (P.earDiagonal i).relInterior := by
    rw [Segment.relInterior, earDiagonal, right_mem_openSegment_iff]; exact hAC
  have hconv : 0 < orient (P.prevVertex i) (P.vertex i) (P.nextVertex i) := h.convex
  rw [eq_empty_iff_forall_notMem]
  rintro x ⟨hx, j, hj⟩
  have hxd : x ∈ (P.earDiagonal i).toSet := Segment.relInterior_subset_toSet _ hx
  by_cases e₁ : j = P.prev (P.prev i)
  · subst e₁
    have := (h.edge_prev_prev_inter_earDiagonal hP h4).subset ⟨hj, hxd⟩
    rw [mem_singleton_iff] at this
    exact hA (this ▸ hx)
  by_cases e₂ : j = P.prev i
  · subst e₂
    rw [edge_toSet, next_prev] at hj
    have h' : orient (P.vertex i) (P.prevVertex i) (P.nextVertex i) ≠ 0 := by
      rw [orient_swap₁₂]; exact neg_ne_zero.mpr hconv.ne'
    have := (Triangle.segment_inter_segment_eq h').subset
      ⟨by rw [segment_symm]; exact hj, hxd⟩
    rw [mem_singleton_iff] at this
    exact hA (this ▸ hx)
  by_cases e₃ : j = i
  · subst e₃
    rw [edge_toSet] at hj
    have h' : orient (P.prevVertex j) (P.nextVertex j) (P.vertex j) ≠ 0 := by
      rw [orient_swap₂₃]; exact neg_ne_zero.mpr hconv.ne'
    have := (Triangle.segment_inter_segment_eq h').subset
      ⟨hxd, by rw [segment_symm]; exact hj⟩
    rw [mem_singleton_iff] at this
    exact hC (this ▸ hx)
  by_cases e₄ : j = P.next i
  · subst e₄
    have := (h.earDiagonal_inter_edge_next hP h4).subset ⟨hxd, hj⟩
    rw [mem_singleton_iff] at this
    exact hC (this ▸ hx)
  exact Set.disjoint_left.mp (h.disjoint_edge_earDiagonal hP e₁ e₂ e₃ e₄) hj hxd

end RawPolygon

end ComputationalGeometry
