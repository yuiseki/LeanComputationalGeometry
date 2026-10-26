import LeanComputationalGeometry.Polygon.Ear
import LeanComputationalGeometry.Polygon.SignedArea
import LeanComputationalGeometry.Polygon.TriangleRegion

/-!
# Cutting off an ear

`removeEar P i` drops vertex `i` from the ring, joining its neighbours by the
ear diagonal. It is built in two steps: `shiftLast` relabels the ring so that
vertex `i` comes last, without changing anything geometric (a `Relabel`), and
`dropLast` drops the last vertex. The ring has one vertex fewer
(`removeEar_n`).

Without any assumption, the edge sums split along the ear:

- `signedArea2_removeEar`: the shoelace sum is the smaller ring's plus the
  ear triangle's;
- `windingNumber_removeEar`: so is the winding number at every point.

For an ear of a simple polygon with at least four vertices, the smaller ring
is again simple (`IsEar.isSimple_removeEar`), and so is a `SimplePolygon`
(`SimplePolygon.removeEar`). Its edges are the polygon's edges other than the
ear's two, and the diagonal; the diagonal meets the old edges only where it
must (`Polygon/Ear.lean`).

The region splits too, `region_removeEar`: the polygon's closed region is the
smaller ring's together with the ear triangle, provided the ear triangle lies
in the polygon's region. That proviso is not derived from `IsEar`. For a
simple counterclockwise polygon it does follow, but the proof needs facts not
yet here: that the winding number is constant off the boundary on connected
sets, and that it is `0` or `1` for a simple counterclockwise polygon (both
consequences of the Jordan curve theorem for polygons). The same facts would
give the disjointness of the smaller ring's open region from the interior of
the ear triangle, which is likewise not proved here.
-/

namespace ComputationalGeometry

open Set Point2D

namespace RawPolygon

/-! ## Relabelling a ring -/

/-- `Q` is `P` with its vertices relabelled by `σ`, keeping their cyclic
order. -/
structure Relabel (Q P : RawPolygon) where
  σ : Fin Q.n ≃ Fin P.n
  vertex_eq : ∀ j, Q.vertex j = P.vertex (σ j)
  next_eq : ∀ j, σ (Q.next j) = P.next (σ j)

namespace Relabel

variable {Q P : RawPolygon} (ρ : Relabel Q P)
include ρ

theorem prev_eq (j : Fin Q.n) : ρ.σ (Q.prev j) = P.prev (ρ.σ j) := by
  apply P.next_injective
  rw [← ρ.next_eq, next_prev, next_prev]

theorem edge_eq (j : Fin Q.n) : Q.edge j = P.edge (ρ.σ j) := by
  simp only [edge, ρ.vertex_eq, ρ.next_eq]

theorem n_eq : Q.n = P.n := by simpa using Fintype.card_congr ρ.σ

theorem sum_edges {M : Type*} [AddCommMonoid M] (g : Point2D → Point2D → M) :
    ∑ j, g (Q.vertex j) (Q.vertex (Q.next j)) = ∑ j, g (P.vertex j) (P.vertex (P.next j)) := by
  simp only [ρ.vertex_eq, ρ.next_eq]
  exact Equiv.sum_comp ρ.σ (fun j => g (P.vertex j) (P.vertex (P.next j)))

theorem signedArea2_eq : Q.signedArea2 = P.signedArea2 := ρ.sum_edges cross

theorem windingNumber_eq (p : Point2D) : Q.windingNumber p = P.windingNumber p :=
  ρ.sum_edges (edgeContribution p)

theorem onBoundary_iff (p : Point2D) : Q.OnBoundary p ↔ P.OnBoundary p := by
  constructor
  · rintro ⟨j, h⟩
    exact ⟨ρ.σ j, ρ.edge_eq j ▸ h⟩
  · rintro ⟨j, h⟩
    refine ⟨ρ.σ.symm j, ?_⟩
    rw [ρ.edge_eq, Equiv.apply_symm_apply]
    exact h

theorem region_eq : Q.region = P.region := by
  ext p
  show Q.OnBoundary p ∨ Q.windingNumber p ≠ 0 ↔ P.OnBoundary p ∨ P.windingNumber p ≠ 0
  rw [ρ.onBoundary_iff, ρ.windingNumber_eq]

theorem openRegion_eq : Q.openRegion = P.openRegion := by
  ext p
  show ¬ Q.OnBoundary p ∧ Q.windingNumber p ≠ 0 ↔
    ¬ P.OnBoundary p ∧ P.windingNumber p ≠ 0
  rw [ρ.onBoundary_iff, ρ.windingNumber_eq]

theorem isSimple (hP : P.IsSimple) : Q.IsSimple where
  three_le := ρ.n_eq ▸ hP.three_le
  edge_nondegenerate j := by
    rw [ρ.edge_eq]
    exact hP.edge_nondegenerate _
  adjacent_inter j := by
    rw [ρ.edge_eq, ρ.edge_eq, ρ.next_eq, ρ.vertex_eq, ρ.next_eq]
    exact hP.adjacent_inter _
  nonadjacent_disjoint i j hij h₁ h₂ := by
    rw [ρ.edge_eq, ρ.edge_eq]
    refine hP.nonadjacent_disjoint _ _ (ρ.σ.injective.ne hij) ?_ ?_
    · rw [← ρ.next_eq]; exact ρ.σ.injective.ne h₁
    · rw [← ρ.next_eq]; exact ρ.σ.injective.ne h₂

theorem earTriangle_eq (j : Fin Q.n) : Q.earTriangle j = P.earTriangle (ρ.σ j) := by
  simp only [earTriangle, prevVertex, nextVertex, ρ.vertex_eq, ρ.prev_eq, ρ.next_eq]

theorem convexVertex_iff (j : Fin Q.n) : Q.ConvexVertex j ↔ P.ConvexVertex (ρ.σ j) := by
  simp only [ConvexVertex, prevVertex, nextVertex, ρ.vertex_eq, ρ.prev_eq, ρ.next_eq]

theorem isEar {j : Fin Q.n} (h : P.IsEar (ρ.σ j)) : Q.IsEar j where
  convex := (ρ.convexVertex_iff j).mpr h.convex
  empty k h₁ h₂ h₃ := by
    rw [ρ.earTriangle_eq, ρ.vertex_eq]
    refine h.empty _ ?_ (ρ.σ.injective.ne h₂) ?_
    · rw [← ρ.prev_eq]; exact ρ.σ.injective.ne h₁
    · rw [← ρ.next_eq]; exact ρ.σ.injective.ne h₃

end Relabel

/-! ## Moving a vertex to the end, and dropping the last vertex -/

/-- The ring relabelled so that vertex `i` comes last. -/
def shiftLast : (P : RawPolygon) → Fin P.n → RawPolygon
  | ⟨0, _⟩, i => i.elim0
  | ⟨m + 1, v⟩, i => ⟨m + 1, fun j => v (j + (i + 1))⟩

/-- The ring without its last vertex. -/
def dropLast : RawPolygon → RawPolygon
  | ⟨0, v⟩ => ⟨0, v⟩
  | ⟨m + 1, v⟩ => ⟨m, v ∘ Fin.castSucc⟩

/-- The ring with vertex `i` dropped, its neighbours joined by the ear
diagonal. -/
def removeEar (P : RawPolygon) (i : Fin P.n) : RawPolygon := (P.shiftLast i).dropLast

theorem removeEar_n (P : RawPolygon) (i : Fin P.n) : (P.removeEar i).n = P.n - 1 := by
  obtain ⟨_ | m, v⟩ := P
  · exact i.elim0
  · rfl

theorem shiftLast_mk {m : ℕ} (v : Fin (m + 1) → Point2D) (i : Fin (m + 1)) :
    shiftLast ⟨m + 1, v⟩ i = ⟨m + 1, fun j => v (j + (i + 1))⟩ := rfl

theorem dropLast_mk {m : ℕ} (v : Fin (m + 1) → Point2D) :
    dropLast ⟨m + 1, v⟩ = ⟨m, v ∘ Fin.castSucc⟩ := rfl

/-- Moving vertex `i` to the end is a relabelling. -/
def shiftLastRelabel {m : ℕ} (v : Fin (m + 1) → Point2D) (i : Fin (m + 1)) :
    Relabel ⟨m + 1, fun j => v (j + (i + 1))⟩ ⟨m + 1, v⟩ where
  σ := Equiv.addRight (i + 1)
  vertex_eq _ := rfl
  next_eq j := by
    show finRotate (m + 1) j + (i + 1) = finRotate (m + 1) (j + (i + 1))
    rw [finRotate_apply, finRotate_apply, add_right_comm]

theorem shiftLastRelabel_last {m : ℕ} (v : Fin (m + 1) → Point2D) (i : Fin (m + 1)) :
    (shiftLastRelabel v i).σ (Fin.last m) = i := by
  show Fin.last m + (i + 1) = i
  rw [add_comm i, ← add_assoc, Fin.last_add_one, zero_add]

/-! ## Dropping the last vertex of a ring

Here `◇v` is the ring with vertices `v`, so that `◇v` with `l + 2` vertices
loses its last vertex to become `◇(v ∘ Fin.castSucc)`.
-/

local notation "◇" v:max => RawPolygon.mk _ v

section DropLast

variable {l : ℕ} (v : Fin (l + 1 + 1) → Point2D)

theorem dropLast_next_last :
    (◇(v ∘ Fin.castSucc)).next (Fin.last l) = 0 := by
  show finRotate (l + 1) (Fin.last l) = 0
  rw [finRotate_apply, Fin.last_add_one]

theorem next_last : (◇v).next (Fin.last (l + 1)) = 0 := by
  show finRotate (l + 1 + 1) (Fin.last (l + 1)) = 0
  rw [finRotate_apply, Fin.last_add_one]

theorem prev_last :
    (◇v).prev (Fin.last (l + 1)) = Fin.castSucc (Fin.last l) := by
  apply (◇v).next_injective
  rw [next_prev]
  show Fin.last (l + 1) = finRotate (l + 1 + 1) (Fin.castSucc (Fin.last l))
  rw [finRotate_apply, Fin.coeSucc_eq_succ, Fin.succ_last]

theorem castSucc_dropLast_next {k : Fin (l + 1)} (hk : k ≠ Fin.last l) :
    Fin.castSucc ((◇(v ∘ Fin.castSucc)).next k) =
      (◇v).next (Fin.castSucc k) := by
  obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr hk
  show Fin.castSucc (finRotate (l + 1) (Fin.castSucc k)) =
    finRotate (l + 1 + 1) (Fin.castSucc (Fin.castSucc k))
  rw [finRotate_apply, finRotate_apply, Fin.coeSucc_eq_succ, Fin.coeSucc_eq_succ,
    Fin.succ_castSucc]

theorem dropLast_edge_of_ne_last {k : Fin (l + 1)} (hk : k ≠ Fin.last l) :
    (◇(v ∘ Fin.castSucc)).edge k =
      (◇v).edge (Fin.castSucc k) := by
  simp only [edge, Function.comp_apply, castSucc_dropLast_next v hk]

theorem dropLast_edge_last :
    (◇(v ∘ Fin.castSucc)).edge (Fin.last l) =
      (◇v).earDiagonal (Fin.last (l + 1)) := by
  simp only [edge, earDiagonal, prevVertex, nextVertex, Function.comp_apply,
    dropLast_next_last, next_last, prev_last, Fin.castSucc_zero]

/-- Each index is the last, the one before, or one kept by `dropLast`. -/
theorem index_cases (j : Fin (l + 1 + 1)) :
    j = Fin.last (l + 1) ∨ j = (◇v).prev (Fin.last (l + 1)) ∨
      ∃ k : Fin (l + 1), k ≠ Fin.last l ∧ j = Fin.castSucc k := by
  rw [prev_last]
  induction j using Fin.lastCases with
  | last => exact Or.inl rfl
  | cast k =>
    by_cases hk : k = Fin.last l
    · exact Or.inr (Or.inl (by rw [hk]))
    · exact Or.inr (Or.inr ⟨k, hk, rfl⟩)

/-- Edge sums split along the ear at the last vertex. -/
theorem sum_edges_dropLast {M : Type*} [AddCommGroup M] (g : Point2D → Point2D → M) :
    ∑ j, g ((◇v).vertex j)
        ((◇v).vertex ((◇v).next j)) =
      ∑ k, g ((◇(v ∘ Fin.castSucc)).vertex k)
          ((◇(v ∘ Fin.castSucc)).vertex
            ((◇(v ∘ Fin.castSucc)).next k)) -
        g ((◇v).prevVertex (Fin.last (l + 1)))
          ((◇v).nextVertex (Fin.last (l + 1))) +
        g ((◇v).prevVertex (Fin.last (l + 1)))
          ((◇v).vertex (Fin.last (l + 1))) +
        g ((◇v).vertex (Fin.last (l + 1)))
          ((◇v).nextVertex (Fin.last (l + 1))) := by
  have hQ : ∀ k : Fin l, g ((◇(v ∘ Fin.castSucc)).vertex (Fin.castSucc k))
      ((◇(v ∘ Fin.castSucc)).vertex ((◇(v ∘ Fin.castSucc)).next (Fin.castSucc k))) =
      g ((◇v).vertex (Fin.castSucc (Fin.castSucc k)))
        ((◇v).vertex ((◇v).next (Fin.castSucc (Fin.castSucc k)))) := by
    intro k
    exact congrArg (fun s : Segment => g s.p s.q)
      (dropLast_edge_of_ne_last v (Fin.castSucc_lt_last k).ne)
  have hQL : g ((◇(v ∘ Fin.castSucc)).vertex (Fin.last l))
      ((◇(v ∘ Fin.castSucc)).vertex ((◇(v ∘ Fin.castSucc)).next (Fin.last l))) =
      g ((◇v).prevVertex (Fin.last (l + 1))) ((◇v).nextVertex (Fin.last (l + 1))) := by
    exact congrArg (fun s : Segment => g s.p s.q) (dropLast_edge_last v)
  have hRL : g ((◇v).vertex (Fin.castSucc (Fin.last l)))
      ((◇v).vertex ((◇v).next (Fin.castSucc (Fin.last l)))) =
      g ((◇v).prevVertex (Fin.last (l + 1))) ((◇v).vertex (Fin.last (l + 1))) := by
    rw [← prev_last, next_prev]
    rfl
  rw [Fin.sum_univ_castSucc (fun j => g ((◇v).vertex j) ((◇v).vertex ((◇v).next j))),
    Fin.sum_univ_castSucc
      (fun k => g ((◇v).vertex (Fin.castSucc k)) ((◇v).vertex ((◇v).next (Fin.castSucc k)))),
    Fin.sum_univ_castSucc (fun k => g ((◇(v ∘ Fin.castSucc)).vertex k)
      ((◇(v ∘ Fin.castSucc)).vertex ((◇(v ∘ Fin.castSucc)).next k)))]
  simp only [hQ, hQL, hRL, nextVertex]
  abel

end DropLast

/-! ## Edge sums of the smaller ring -/

theorem removeEar_mk {l : ℕ} (v : Fin (l + 1 + 1) → Point2D) (i : Fin (l + 1 + 1)) :
    removeEar ⟨l + 1 + 1, v⟩ i = ⟨l + 1, (fun j => v (j + (i + 1))) ∘ Fin.castSucc⟩ := rfl

/-- The ear triangle at vertex `i` is the ear triangle at the last vertex once
`i` is moved to the end. -/
theorem earTriangle_shiftLast {l : ℕ} (v : Fin (l + 1 + 1) → Point2D) (i : Fin (l + 1 + 1)) :
    (◇fun j => v (j + (i + 1))).earTriangle (Fin.last (l + 1)) =
      (◇v).earTriangle i := by
  rw [(shiftLastRelabel v i).earTriangle_eq, shiftLastRelabel_last]

/-- Edge sums split along the ear: the smaller ring's, less the diagonal, plus
the ear's two edges. -/
theorem sum_edges_removeEar {M : Type*} [AddCommGroup M] (g : Point2D → Point2D → M)
    (P : RawPolygon) (h2 : 2 ≤ P.n) (i : Fin P.n) :
    ∑ j, g (P.vertex j) (P.vertex (P.next j)) =
      ∑ k, g ((P.removeEar i).vertex k) ((P.removeEar i).vertex ((P.removeEar i).next k)) -
        g (P.prevVertex i) (P.nextVertex i) + g (P.prevVertex i) (P.vertex i) +
          g (P.vertex i) (P.nextVertex i) := by
  obtain ⟨_ | _ | l, v⟩ := P
  · exact i.elim0
  · exact absurd h2 (by norm_num)
  have hT := earTriangle_shiftLast v i
  have e₁ : (◇fun j => v (j + (i + 1))).prevVertex (Fin.last (l + 1)) =
      (◇v).prevVertex i := congrArg Triangle.a hT
  have e₂ : (◇fun j => v (j + (i + 1))).vertex (Fin.last (l + 1)) =
      (◇v).vertex i := congrArg Triangle.b hT
  have e₃ : (◇fun j => v (j + (i + 1))).nextVertex (Fin.last (l + 1)) =
      (◇v).nextVertex i := congrArg Triangle.c hT
  rw [removeEar_mk, ← (shiftLastRelabel v i).sum_edges g, sum_edges_dropLast, e₁, e₂, e₃]

/-- The shoelace sum splits along an ear: the smaller ring's plus the ear
triangle's. -/
theorem signedArea2_removeEar (P : RawPolygon) (h2 : 2 ≤ P.n) (i : Fin P.n) :
    P.signedArea2 = (P.removeEar i).signedArea2 + (P.earTriangle i).signedArea2 := by
  have := sum_edges_removeEar cross P h2 i
  rw [Triangle.signedArea2_eq_cross_sum]
  simp only [signedArea2, earTriangle]
  rw [this, cross_comm (P.prevVertex i) (P.nextVertex i)]
  abel

/-- The winding number splits along an ear: the smaller ring's plus the ear
triangle's. -/
theorem windingNumber_removeEar (P : RawPolygon) (h2 : 2 ≤ P.n) (i : Fin P.n) (p : Point2D) :
    P.windingNumber p = (P.removeEar i).windingNumber p + (P.earTriangle i).winding3 p := by
  have := sum_edges_removeEar (edgeContribution p) P h2 i
  simp only [windingNumber, Triangle.winding3, earTriangle]
  rw [this, edgeContribution_swap p (P.prevVertex i) (P.nextVertex i)]
  abel

/-! ## The smaller ring is simple -/

section DropLastSimple

variable {l : ℕ} (v : Fin (l + 1 + 1) → Point2D)

/-- Edges away from the ear at the last vertex miss the diagonal. -/
theorem disjoint_dropLast_edge_earDiagonal (hR : (◇v).IsSimple)
    (hear : (◇v).IsEar (Fin.last (l + 1))) {b : Fin (l + 1)} (hb : b ≠ Fin.last l)
    (h₁ : (◇(v ∘ Fin.castSucc)).next (Fin.last l) ≠ b)
    (h₂ : (◇(v ∘ Fin.castSucc)).next b ≠ Fin.last l) :
    Disjoint ((◇v).edge (Fin.castSucc b)).toSet
      ((◇v).earDiagonal (Fin.last (l + 1))).toSet := by
  apply hear.disjoint_edge_earDiagonal hR
  · intro e
    apply h₂
    apply Fin.castSucc_injective
    rw [castSucc_dropLast_next v hb, e, next_prev, prev_last]
  · rw [prev_last]
    exact (Fin.castSucc_injective _).ne hb
  · exact (Fin.castSucc_lt_last b).ne
  · intro e
    rw [dropLast_next_last] at h₁
    apply h₁
    apply Fin.castSucc_injective
    rw [e, next_last, Fin.castSucc_zero]

/-- Cutting the ear at the last vertex of a simple polygon with at least four
vertices leaves a simple polygon. -/
theorem isSimple_dropLast (hR : (◇v).IsSimple) (h4 : 4 ≤ l + 1 + 1)
    (hear : (◇v).IsEar (Fin.last (l + 1))) : (◇(v ∘ Fin.castSucc)).IsSimple := by
  have h0 : (0 : Fin (l + 1)) ≠ Fin.last l := by
    rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_last]
    omega
  refine ⟨by show 3 ≤ l + 1; omega, fun k => ?_, fun k => ?_, fun a b hab h₁ h₂ => ?_⟩
  · by_cases hk : k = Fin.last l
    · subst hk
      rw [dropLast_edge_last]
      exact hear.prevVertex_ne_nextVertex
    · rw [dropLast_edge_of_ne_last v hk]
      exact hR.edge_nondegenerate _
  · by_cases hk : k = Fin.last l
    · subst hk
      show _ = {v (Fin.castSucc ((◇(v ∘ Fin.castSucc)).next (Fin.last l)))}
      rw [dropLast_edge_last, dropLast_next_last, dropLast_edge_of_ne_last v h0,
        Fin.castSucc_zero, ← next_last v]
      exact hear.earDiagonal_inter_edge_next hR h4
    · show _ = {v (Fin.castSucc ((◇(v ∘ Fin.castSucc)).next k))}
      rw [dropLast_edge_of_ne_last v hk]
      by_cases hk' : (◇(v ∘ Fin.castSucc)).next k = Fin.last l
      · have hpp : Fin.castSucc k = (◇v).prev ((◇v).prev (Fin.last (l + 1))) := by
          apply (◇v).next_injective
          rw [next_prev, ← castSucc_dropLast_next v hk, hk', prev_last]
        rw [hk', dropLast_edge_last, hpp, ← prev_last v]
        exact hear.edge_prev_prev_inter_earDiagonal hR h4
      · rw [dropLast_edge_of_ne_last v hk', castSucc_dropLast_next v hk]
        exact hR.adjacent_inter _
  · by_cases ha : a = Fin.last l <;> by_cases hb : b = Fin.last l
    · exact absurd (ha.trans hb.symm) hab
    · subst ha
      rw [dropLast_edge_last, dropLast_edge_of_ne_last v hb]
      exact (disjoint_dropLast_edge_earDiagonal v hR hear hb h₁ h₂).symm
    · subst hb
      rw [dropLast_edge_last, dropLast_edge_of_ne_last v ha]
      exact disjoint_dropLast_edge_earDiagonal v hR hear ha h₂ h₁
    · rw [dropLast_edge_of_ne_last v ha, dropLast_edge_of_ne_last v hb]
      refine hR.nonadjacent_disjoint _ _ ((Fin.castSucc_injective _).ne hab) ?_ ?_
      · rw [← castSucc_dropLast_next v ha]
        exact (Fin.castSucc_injective _).ne h₁
      · rw [← castSucc_dropLast_next v hb]
        exact (Fin.castSucc_injective _).ne h₂

/-- The winding number splits along the ear at the last vertex. -/
theorem windingNumber_dropLast (p : Point2D) :
    (◇v).windingNumber p =
      (◇(v ∘ Fin.castSucc)).windingNumber p +
        ((◇v).earTriangle (Fin.last (l + 1))).winding3 p := by
  have := sum_edges_dropLast v (edgeContribution p)
  simp only [windingNumber, Triangle.winding3, earTriangle]
  rw [this, edgeContribution_swap p ((◇v).prevVertex (Fin.last (l + 1)))
    ((◇v).nextVertex (Fin.last (l + 1)))]
  abel

/-- The region splits along the ear at the last vertex, if the ear triangle
lies in the region. -/
theorem region_dropLast (hconv : (◇v).ConvexVertex (Fin.last (l + 1)))
    (hin : ((◇v).earTriangle (Fin.last (l + 1))).toSet ⊆ (◇v).region) :
    (◇v).region =
      (◇(v ∘ Fin.castSucc)).region ∪ ((◇v).earTriangle (Fin.last (l + 1))).toSet := by
  have hT : ((◇v).earTriangle (Fin.last (l + 1))).IsCCW := hconv
  have hab :
      segment ℝ ((◇v).prevVertex (Fin.last (l + 1))) ((◇v).vertex (Fin.last (l + 1))) ⊆
      ((◇v).earTriangle (Fin.last (l + 1))).toSet :=
    Triangle.segment_subset_toSet (by simp [earTriangle]) (by simp [earTriangle])
  have hbc :
      segment ℝ ((◇v).vertex (Fin.last (l + 1))) ((◇v).nextVertex (Fin.last (l + 1))) ⊆
      ((◇v).earTriangle (Fin.last (l + 1))).toSet :=
    Triangle.segment_subset_toSet (by simp [earTriangle]) (by simp [earTriangle])
  have hw0 : ∀ p, p ∉ ((◇v).earTriangle (Fin.last (l + 1))).toSet →
      ((◇v).earTriangle (Fin.last (l + 1))).winding3 p = 0 := by
    intro p hp
    rw [← Triangle.mem_region_toPolygon_iff_of_isCCW hT] at hp
    rw [← Triangle.windingNumber_toPolygon]
    by_contra hne
    exact hp (Or.inr hne)
  ext p
  constructor
  · intro hp
    by_cases hpT : p ∈ ((◇v).earTriangle (Fin.last (l + 1))).toSet
    · exact Or.inr hpT
    left
    change (◇v).OnBoundary p ∨ (◇v).windingNumber p ≠ 0 at hp
    show (◇(v ∘ Fin.castSucc)).OnBoundary p ∨ (◇(v ∘ Fin.castSucc)).windingNumber p ≠ 0
    rcases hp with ⟨j, hj⟩ | hw
    · rcases index_cases v j with rfl | rfl | ⟨k, hk, rfl⟩
      · exact absurd (hbc hj) hpT
      · rw [edge_toSet, next_prev] at hj
        exact absurd (hab hj) hpT
      · exact Or.inl ⟨k, by rw [dropLast_edge_of_ne_last v hk]; exact hj⟩
    · right
      rw [windingNumber_dropLast, hw0 p hpT, add_zero] at hw
      exact hw
  · rintro (hp | hp)
    · by_cases hpT : p ∈ ((◇v).earTriangle (Fin.last (l + 1))).toSet
      · exact hin hpT
      change (◇(v ∘ Fin.castSucc)).OnBoundary p ∨
        (◇(v ∘ Fin.castSucc)).windingNumber p ≠ 0 at hp
      show (◇v).OnBoundary p ∨ (◇v).windingNumber p ≠ 0
      rcases hp with ⟨k, hk⟩ | hw
      · by_cases hkl : k = Fin.last l
        · subst hkl
          rw [dropLast_edge_last] at hk
          exact absurd (earDiagonal_subset_earTriangle _ hk) hpT
        · rw [dropLast_edge_of_ne_last v hkl] at hk
          exact Or.inl ⟨_, hk⟩
      · right
        rw [windingNumber_dropLast, hw0 p hpT, add_zero]
        exact hw
    · exact hin hp

end DropLastSimple

/-! ## The general statements -/

/-- Cutting an ear off a simple polygon with at least four vertices leaves a
simple polygon. -/
theorem IsEar.isSimple_removeEar {P : RawPolygon} (hP : P.IsSimple) (h4 : 4 ≤ P.n) {i : Fin P.n}
    (h : P.IsEar i) : (P.removeEar i).IsSimple := by
  obtain ⟨_ | _ | l, v⟩ := P
  · exact i.elim0
  · exact absurd h4 (by norm_num)
  rw [removeEar_mk]
  refine isSimple_dropLast (fun j => v (j + (i + 1))) ((shiftLastRelabel v i).isSimple hP) h4
    ((shiftLastRelabel v i).isEar ?_)
  rw [shiftLastRelabel_last]
  exact h

/-- The region splits along an ear: the closed region is the smaller ring's
together with the ear triangle, provided the ear triangle lies in the region.
The proviso is not derived here; see the module docstring. -/
theorem region_removeEar {P : RawPolygon} (h2 : 2 ≤ P.n) {i : Fin P.n} (hconv : P.ConvexVertex i)
    (hin : (P.earTriangle i).toSet ⊆ P.region) :
    P.region = (P.removeEar i).region ∪ (P.earTriangle i).toSet := by
  obtain ⟨_ | _ | l, v⟩ := P
  · exact i.elim0
  · exact absurd h2 (by norm_num)
  rw [removeEar_mk, ← (shiftLastRelabel v i).region_eq, ← earTriangle_shiftLast v i]
  refine region_dropLast (fun j => v (j + (i + 1))) ?_ ?_
  · rw [(shiftLastRelabel v i).convexVertex_iff, shiftLastRelabel_last]
    exact hconv
  · rw [earTriangle_shiftLast, (shiftLastRelabel v i).region_eq]
    exact hin

end RawPolygon

namespace SimplePolygon

/-- A simple polygon with an ear cut off, given at least four vertices. -/
def removeEar (P : SimplePolygon) (h4 : 4 ≤ P.1.n) (i : Fin P.1.n) (h : P.1.IsEar i) :
    SimplePolygon :=
  ⟨P.1.removeEar i, h.isSimple_removeEar P.2 h4⟩

theorem removeEar_n (P : SimplePolygon) (h4 : 4 ≤ P.1.n) (i : Fin P.1.n) (h : P.1.IsEar i) :
    (P.removeEar h4 i h).1.n = P.1.n - 1 :=
  P.1.removeEar_n i

theorem toRegion_removeEar (P : SimplePolygon) (h4 : 4 ≤ P.1.n) (i : Fin P.1.n) (h : P.1.IsEar i)
    (hin : (P.1.earTriangle i).toSet ⊆ P.toRegion) :
    P.toRegion = (P.removeEar h4 i h).toRegion ∪ (P.1.earTriangle i).toSet :=
  RawPolygon.region_removeEar (by omega) h.convex hin

end SimplePolygon

end ComputationalGeometry
