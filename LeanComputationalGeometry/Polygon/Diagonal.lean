import LeanComputationalGeometry.Polygon.Jordan

/-!
# Diagonals and the two sides of a diagonal

`P.chain i k` is the ring of the `k + 1` vertices from vertex `i` on, `k`
steps along `P`, closed up by the segment from the last back to `i`. Its first
`k` edges are edges of `P`, its last edge is the closing segment. A diagonal
`IsDiagonal P i k` is a closing segment that runs inside the open region of
`P`, with at least two steps on either side. The diagonal then splits `P`
into `P.chain i k` and the chain on the other side,
`P.chain (P.next^[k] i) (P.n - k)`, which runs along the rest of the ring and
back along the diagonal the other way.

- The winding numbers of the two sides add up to the winding number of `P`,
  at every point (`windingNumber_chain_add`): the diagonal is traversed once
  each way and cancels.
- For a simple polygon both sides are simple (`IsDiagonal.isSimple_chain`).
- For a simple polygon that winds `0` or `1` times, so do both sides, their
  open regions lie in the open region of `P`, and they are disjoint
  (`IsDiagonal.windsZeroOrOne_chain`, `IsDiagonal.openRegion_chain_subset`,
  `IsDiagonal.disjoint_openRegion_chain`).

Nothing here constructs a diagonal; that is done in `Polygon/TwoEars.lean`.
-/

namespace ComputationalGeometry

open Set Point2D Filter Topology

namespace RawPolygon

variable {P : RawPolygon}

/-! ## Steps along the ring -/

theorem iterate_next_add (i : Fin P.n) (a b : ℕ) :
    P.next^[a + b] i = P.next^[a] (P.next^[b] i) := Function.iterate_add_apply _ _ _ _

/-- Going all the way round comes back. -/
theorem iterate_next_n (i : Fin P.n) : P.next^[P.n] i = i := by
  ext
  rw [val_iterate_next, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

/-- Fewer than `n` steps from one vertex reach different vertices. -/
theorem iterate_next_inj (i : Fin P.n) {a b : ℕ} (ha : a < P.n) (hb : b < P.n)
    (h : P.next^[a] i = P.next^[b] i) : a = b := by
  by_contra hab
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · apply P.iterate_next_ne (P.next^[a] i) (k := b - a) (by omega) (by omega)
    rw [← iterate_next_add, Nat.sub_add_cancel hlt.le, h]
  · apply P.iterate_next_ne (P.next^[b] i) (k := a - b) (by omega) (by omega)
    rw [← iterate_next_add, Nat.sub_add_cancel hlt.le, h]

/-- Summing over the vertices in ring order from any vertex is summing over
all vertices. -/
theorem sum_range_iterate_next {M : Type*} [AddCommMonoid M] (i : Fin P.n) (f : Fin P.n → M) :
    ∑ m ∈ Finset.range P.n, f (P.next^[m] i) = ∑ j, f j := by
  have hinj : Function.Injective fun m : Fin P.n => P.next^[m.val] i :=
    fun a b h => Fin.ext (iterate_next_inj i a.isLt b.isLt h)
  rw [← Fin.sum_univ_eq_sum_range (fun m => f (P.next^[m] i))]
  exact Equiv.sum_comp (Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)) f

/-! ## Chains -/

variable (P) in
/-- The `k + 1` vertices from vertex `i` on, as a ring: `k` edges of `P`, then
the segment back to vertex `i`. -/
def chain (i : Fin P.n) (k : ℕ) : RawPolygon := ⟨k + 1, fun m => P.vertex (P.next^[m.val] i)⟩

theorem chain_n (i : Fin P.n) (k : ℕ) : (P.chain i k).n = k + 1 := rfl

theorem chain_vertex (i : Fin P.n) (k : ℕ) (m : Fin (P.chain i k).n) :
    (P.chain i k).vertex m = P.vertex (P.next^[m.val] i) := rfl

theorem chain_val_next {i : Fin P.n} {k : ℕ} (m : Fin (P.chain i k).n) :
    ((P.chain i k).next m).val = (m.val + 1) % (k + 1) := val_next _ m

/-- The vertex after an inner vertex of a chain is the next vertex of `P`. -/
theorem chain_vertex_next_of_lt {i : Fin P.n} {k : ℕ} (m : Fin (P.chain i k).n) (hm : m.val < k) :
    (P.chain i k).vertex ((P.chain i k).next m) = P.vertex (P.next (P.next^[m.val] i)) := by
  rw [chain_vertex, chain_val_next, Nat.mod_eq_of_lt (by omega),
    ← Function.iterate_succ_apply' P.next]

/-- The vertex after the last vertex of a chain is its first. -/
theorem chain_vertex_next_last {i : Fin P.n} {k : ℕ} (m : Fin (P.chain i k).n) (hm : m.val = k) :
    (P.chain i k).vertex ((P.chain i k).next m) = P.vertex i := by
  rw [chain_vertex, chain_val_next, hm, Nat.mod_self]
  rfl

/-- The edges of a chain: edges of `P`, then the closing segment. -/
theorem chain_edge_of_lt {i : Fin P.n} {k : ℕ} (m : Fin (P.chain i k).n) (hm : m.val < k) :
    (P.chain i k).edge m = P.edge (P.next^[m.val] i) := by
  simp only [edge, chain_vertex_next_of_lt m hm, chain_vertex]

theorem chain_edge_last {i : Fin P.n} {k : ℕ} (m : Fin (P.chain i k).n) (hm : m.val = k) :
    (P.chain i k).edge m = ⟨P.vertex (P.next^[k] i), P.vertex i⟩ := by
  simp only [edge, chain_vertex_next_last m hm, chain_vertex, hm]

/-- A sum over the edges of a chain. -/
theorem sum_edges_chain {M : Type*} [AddCommMonoid M] (g : Point2D → Point2D → M) (i : Fin P.n)
    (k : ℕ) :
    ∑ m, g ((P.chain i k).vertex m) ((P.chain i k).vertex ((P.chain i k).next m)) =
      ∑ m ∈ Finset.range k, g (P.vertex (P.next^[m] i)) (P.vertex (P.next (P.next^[m] i))) +
        g (P.vertex (P.next^[k] i)) (P.vertex i) := by
  show ∑ m : Fin (k + 1), _ = _
  rw [Fin.sum_univ_castSucc, ← Fin.sum_univ_eq_sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [chain_vertex_next_of_lt (P := P) (i := i) (Fin.castSucc m) m.isLt]
    rfl
  · rw [chain_vertex_next_last (P := P) (i := i) (Fin.last k) rfl]
    rfl

/-- The winding numbers of the two chains on either side of a closing
segment add up to the winding number of the ring: the segment is traversed
once each way. -/
theorem windingNumber_chain_add (i : Fin P.n) {k : ℕ} (hk : k ≤ P.n) (p : Point2D) :
    (P.chain i k).windingNumber p + (P.chain (P.next^[k] i) (P.n - k)).windingNumber p =
      P.windingNumber p := by
  have e₁ := sum_edges_chain (edgeContribution p) i k
  have e₂ := sum_edges_chain (edgeContribution p) (P.next^[k] i) (P.n - k)
  have hz : P.next^[P.n - k] (P.next^[k] i) = i := by
    rw [← iterate_next_add, Nat.sub_add_cancel hk, iterate_next_n]
  rw [hz] at e₂
  unfold windingNumber
  rw [e₁, e₂, ← sum_range_iterate_next i (fun j => edgeContribution p (P.vertex j)
    (P.vertex (P.next j))),
    show Finset.range P.n = Finset.range (k + (P.n - k)) by rw [Nat.add_sub_cancel' hk],
    Finset.sum_range_add]
  simp only [← iterate_next_add]
  have hs := edgeContribution_swap p (P.vertex i) (P.vertex (P.next^[k] i))
  simp only [Nat.add_comm _ k]
  rw [hs]
  abel

/-- A point on a chain is on the ring or on the closing segment. -/
theorem onBoundary_chain_iff (i : Fin P.n) (k : ℕ) (p : Point2D) :
    (P.chain i k).OnBoundary p ↔
      (∃ m < k, p ∈ (P.edge (P.next^[m] i)).toSet) ∨
        p ∈ segment ℝ (P.vertex (P.next^[k] i)) (P.vertex i) := by
  constructor
  · rintro ⟨m, hm⟩
    rcases Nat.lt_or_ge m.val k with h | h
    · rw [chain_edge_of_lt m h] at hm
      exact Or.inl ⟨m.val, h, hm⟩
    · rw [chain_edge_last m (by have := m.isLt; simp only [chain_n] at this; omega)] at hm
      exact Or.inr hm
  · rintro (⟨m, hm, hp⟩ | hp)
    · refine ⟨⟨m, by simp only [chain_n]; omega⟩, ?_⟩
      rwa [chain_edge_of_lt _ hm]
    · refine ⟨⟨k, by simp only [chain_n]; omega⟩, ?_⟩
      rwa [chain_edge_last _ rfl]

/-! ## Diagonals -/

/-- In a simple polygon different vertices are different points. -/
theorem IsSimple.vertex_injective (hP : P.IsSimple) : Function.Injective P.vertex := by
  intro a b h
  rcases hP.vertex_mem_edge (j := a) (k := b) (by rw [← h]; exact (P.edge a).p_mem_toSet) with e | e
  · exact e
  · exact absurd (h.trans (congrArg P.vertex e.symm)) (hP.edge_nondegenerate a)

variable (P) in
/-- The segment from vertex `i` to the vertex `k` steps on is a diagonal: at
least two steps on either side, and the segment, but for its ends, runs in the
open region. -/
structure IsDiagonal (i : Fin P.n) (k : ℕ) : Prop where
  two_le : 2 ≤ k
  add_two_le : k + 2 ≤ P.n
  openSegment_subset : openSegment ℝ (P.vertex i) (P.vertex (P.next^[k] i)) ⊆ P.openRegion

namespace IsDiagonal

variable {i : Fin P.n} {k : ℕ}

theorem not_onBoundary (hD : P.IsDiagonal i k) {x : Point2D}
    (hx : x ∈ openSegment ℝ (P.vertex i) (P.vertex (P.next^[k] i))) : ¬ P.OnBoundary x :=
  (hD.openSegment_subset hx).1

theorem vertex_ne (hD : P.IsDiagonal i k) : P.vertex i ≠ P.vertex (P.next^[k] i) := by
  intro h
  apply hD.not_onBoundary (x := P.vertex i) _ (P.onBoundary_vertex i)
  rw [← h, openSegment_same]
  rfl

/-- The same diagonal, seen from its other end. -/
theorem symm (hD : P.IsDiagonal i k) : P.IsDiagonal (P.next^[k] i) (P.n - k) where
  two_le := by have := hD.add_two_le; omega
  add_two_le := by have := hD.two_le; have := hD.add_two_le; omega
  openSegment_subset := by
    rw [← iterate_next_add, Nat.sub_add_cancel (by have := hD.add_two_le; omega), iterate_next_n,
      openSegment_symm]
    exact hD.openSegment_subset

/-- A point of the closed diagonal on the boundary is one of its ends. -/
theorem eq_or_eq_of_onBoundary (hD : P.IsDiagonal i k) {x : Point2D}
    (hx : x ∈ segment ℝ (P.vertex i) (P.vertex (P.next^[k] i))) (hb : P.OnBoundary x) :
    x = P.vertex i ∨ x = P.vertex (P.next^[k] i) := by
  rw [← insert_endpoints_openSegment] at hx
  rcases hx with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd hb (hD.not_onBoundary h)

/-- The diagonal meets an edge of the chain on its side only at an end, and
only where the edge ends at it. -/
theorem mem_edge (hP : P.IsSimple) (hD : P.IsDiagonal i k) {m : ℕ} (hm : m < k) {x : Point2D}
    (hx : x ∈ segment ℝ (P.vertex i) (P.vertex (P.next^[k] i)))
    (he : x ∈ (P.edge (P.next^[m] i)).toSet) :
    (m = 0 ∧ x = P.vertex i) ∨ (m + 1 = k ∧ x = P.vertex (P.next^[k] i)) := by
  have hn := hD.add_two_le
  rcases hD.eq_or_eq_of_onBoundary hx ⟨_, he⟩ with rfl | rfl
  · left
    refine ⟨?_, rfl⟩
    rcases hP.vertex_mem_edge he with e | e
    · exact iterate_next_inj i (by omega) (by omega) (e.trans (by rfl : i = P.next^[0] i))
    · rw [← Function.iterate_succ_apply' P.next] at e
      exact absurd (iterate_next_inj i (by omega) (by omega)
        (e.trans (by rfl : i = P.next^[0] i))) (by omega)
  · right
    refine ⟨?_, rfl⟩
    rcases hP.vertex_mem_edge he with e | e
    · exact absurd (iterate_next_inj i (by omega) (by omega) e) (by omega)
    · rw [← Function.iterate_succ_apply' P.next] at e
      exact iterate_next_inj i (by omega) (by omega) e

/-- The chain on one side of a diagonal of a simple polygon is simple. -/
theorem isSimple_chain (hP : P.IsSimple) (hD : P.IsDiagonal i k) : (P.chain i k).IsSimple := by
  have hk2 := hD.two_le
  have hn := hD.add_two_le
  set Q := P.chain i k
  have hval : ∀ m : Fin Q.n, (Q.next m).val = (m.val + 1) % (k + 1) := chain_val_next
  have hlt : ∀ m : Fin Q.n, m.val < k + 1 := fun m => m.isLt
  -- Consecutive edges of `P` in the chain.
  have hstep : ∀ m : ℕ, P.next^[m + 1] i = P.next (P.next^[m] i) := fun m =>
    Function.iterate_succ_apply' P.next m i
  refine ⟨by simp only [Q, chain_n]; omega, fun m => ?_, fun m => ?_, fun a b hab h₁ h₂ => ?_⟩
  · rcases Nat.lt_or_ge m.val k with hm | hm
    · rw [chain_edge_of_lt m hm]; exact hP.edge_nondegenerate _
    · rw [chain_edge_last m (by have := hlt m; omega)]
      exact hD.vertex_ne.symm
  · rcases Nat.lt_or_ge (m.val + 1) k with hm | hm
    · have hm' : (Q.next m).val = m.val + 1 := by rw [hval]; exact Nat.mod_eq_of_lt (by omega)
      rw [chain_edge_of_lt m (by omega), chain_edge_of_lt (Q.next m) (by omega),
        chain_vertex_next_of_lt m (by omega), hm', hstep]
      exact hP.adjacent_inter _
    rcases Nat.lt_or_ge m.val k with hm₂ | hm₂
    · -- the last edge of `P` and the closing segment
      have hm' : (Q.next m).val = k := by rw [hval]; rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [chain_edge_of_lt m hm₂, chain_edge_last (Q.next m) hm', chain_vertex_next_of_lt m hm₂]
      have hz : P.next (P.next^[m.val] i) = P.next^[k] i := by
        rw [← hstep]; congr 1; omega
      rw [hz]
      apply Subset.antisymm
      · rintro x ⟨hx₁, hx₂⟩
        rcases hD.mem_edge hP hm₂ (by rw [Segment.toSet, segment_symm] at hx₂; exact hx₂) hx₁ with
          ⟨h0, rfl⟩ | ⟨-, rfl⟩
        · omega
        · rfl
      · rintro x rfl
        refine ⟨?_, (Segment.p_mem_toSet _)⟩
        rw [← hz]; exact (P.edge _).q_mem_toSet
    · -- the closing segment and the first edge
      have hmk : m.val = k := by have := hlt m; omega
      have hm' : (Q.next m).val = 0 := by rw [hval, hmk, Nat.mod_self]
      rw [chain_edge_last m hmk, chain_edge_of_lt (Q.next m) (by omega),
        chain_vertex_next_last m hmk, hm']
      apply Subset.antisymm
      · rintro x ⟨hx₁, hx₂⟩
        rcases hD.mem_edge hP (m := 0) (by omega)
          (by rw [Segment.toSet, segment_symm] at hx₁; exact hx₁) hx₂ with ⟨-, rfl⟩ | ⟨h1, -⟩
        · rfl
        · omega
      · rintro x rfl
        exact ⟨Segment.q_mem_toSet _, (P.edge i).p_mem_toSet⟩
  · rw [Set.disjoint_left]
    intro x hxa hxb
    have hva := hval a
    have hvb := hval b
    have ha := hlt a
    have hb := hlt b
    have hab' : a.val ≠ b.val := fun e => hab (Fin.ext e)
    have h₁' : (Q.next a).val ≠ b.val := fun e => h₁ (Fin.ext e)
    have h₂' : (Q.next b).val ≠ a.val := fun e => h₂ (Fin.ext e)
    rcases Nat.lt_or_ge a.val k with hak | hak <;> rcases Nat.lt_or_ge b.val k with hbk | hbk
    · rw [chain_edge_of_lt a hak] at hxa
      rw [chain_edge_of_lt b hbk] at hxb
      rw [Nat.mod_eq_of_lt (by omega)] at hva hvb
      refine Set.disjoint_left.mp (hP.nonadjacent_disjoint _ _ ?_ ?_ ?_) hxa hxb
      · exact fun e => hab' (iterate_next_inj i (by omega) (by omega) e)
      · rw [← hstep]
        exact fun e => h₁' (by rw [hva]; exact iterate_next_inj i (by omega) (by omega) e)
      · rw [← hstep]
        exact fun e => h₂' (by rw [hvb]; exact iterate_next_inj i (by omega) (by omega) e)
    · rw [chain_edge_of_lt a hak] at hxa
      rw [chain_edge_last b (by omega)] at hxb
      rcases hD.mem_edge hP hak (by rw [Segment.toSet, segment_symm] at hxb; exact hxb) hxa with
        ⟨h0, -⟩ | ⟨h1, -⟩
      · apply h₂'; rw [hvb, show b.val = k by omega, Nat.mod_self, h0]
      · apply h₁'; rw [hva, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [chain_edge_last a (by omega)] at hxa
      rw [chain_edge_of_lt b hbk] at hxb
      rcases hD.mem_edge hP hbk (by rw [Segment.toSet, segment_symm] at hxa; exact hxa) hxb with
        ⟨h0, -⟩ | ⟨h1, -⟩
      · apply h₁'; rw [hva, show a.val = k by omega, Nat.mod_self, h0]
      · apply h₂'; rw [hvb, Nat.mod_eq_of_lt (by omega)]; omega
    · exact hab' (by omega)

end IsDiagonal

end RawPolygon

end ComputationalGeometry
