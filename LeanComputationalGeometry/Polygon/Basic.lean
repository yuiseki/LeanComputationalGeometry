import LeanComputationalGeometry.Triangle
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Polygons: raw rings and simple polygons

Three levels are kept apart, and only the first two exist yet.

1. Raw ring data, `RawPolygon`: `n` vertices `vertex : Fin n → Point2D`,
   joined cyclically, the edge from vertex `i` going to vertex `next i`
   (Mathlib's `finRotate`). Nothing is assumed: edges may cross, vanish or
   overlap, and the data need not describe a region. `RawPolygon.ofList`
   reads a list of vertices, as GIS rings usually come.
2. Simple polygons, `RawPolygon.IsSimple`: at least three vertices, no
   zero-length edge, consecutive edges meeting only at their shared vertex,
   and other edges disjoint. `SimplePolygon` is the subtype.
3. Region semantics, the interior a simple polygon bounds, is not defined
   here yet. It is the next step of the roadmap (winding number,
   point-in-polygon), and nothing in this file presumes it.

A nondegenerate triangle is a simple polygon (`Triangle.isSimple_toPolygon`).
-/

namespace ComputationalGeometry

open Set

/-- Reversing the order of `Fin n` turns the cyclic successor into the
cyclic predecessor. -/
theorem finRotate_rev_finRotate :
    ∀ {n : ℕ} (i : Fin n), finRotate n (Fin.rev (finRotate n i)) = Fin.rev i
  | 0, i => i.elim0
  | 1, _ => Subsingleton.elim _ _
  | k + 2, i => by
    rw [finRotate_apply, finRotate_apply]
    ext
    have hi := i.isLt
    simp only [Fin.val_add, Fin.val_rev, Fin.val_one]
    rcases Nat.lt_or_ge i.val (k + 1) with h | h
    · rw [Nat.mod_eq_of_lt (by omega : i.val + 1 < k + 2)]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · have h' : i.val = k + 1 := by omega
      rw [h', show k + 1 + 1 = k + 2 by rfl, Nat.mod_self]
      simp

/-- A ring of `n` vertices, joined cyclically. Raw data: nothing is assumed. -/
structure RawPolygon where
  /-- The number of vertices. -/
  n : ℕ
  /-- The vertices, in order. -/
  vertex : Fin n → Point2D

namespace RawPolygon

variable (P : RawPolygon)

/-- A ring from a list of vertices. -/
def ofList (l : List Point2D) : RawPolygon := ⟨l.length, l.get⟩

/-- The index of the next vertex, cyclically. -/
def next (i : Fin P.n) : Fin P.n := finRotate P.n i

/-- The index of the previous vertex, cyclically. -/
def prev (i : Fin P.n) : Fin P.n := (finRotate P.n).symm i

@[simp] theorem next_prev (i : Fin P.n) : P.next (P.prev i) = i :=
  (finRotate P.n).apply_symm_apply i

@[simp] theorem prev_next (i : Fin P.n) : P.prev (P.next i) = i :=
  (finRotate P.n).symm_apply_apply i

/-- The edge from vertex `i` to the next vertex. -/
def edge (i : Fin P.n) : Segment := ⟨P.vertex i, P.vertex (P.next i)⟩

/-- The ring moved by `v`. -/
def translate (v : Point2D) : RawPolygon := ⟨P.n, fun i => P.vertex i + v⟩

/-- The same ring, started one vertex later. -/
def rotate : RawPolygon := ⟨P.n, P.vertex ∘ finRotate P.n⟩

/-- The same ring, traversed the other way: vertex `i` of the reverse is
vertex `rev i`. Its edges are the ring's edges, each reversed
(`reverse_edge`). -/
def reverse : RawPolygon := ⟨P.n, fun i => P.vertex (Fin.rev i)⟩

/-- Reversal turns the cyclic successor into the cyclic predecessor. -/
theorem rev_finRotate {n : ℕ} (i : Fin n) :
    Fin.rev (finRotate n i) = (finRotate n).symm (Fin.rev i) := by
  apply (finRotate n).injective
  rw [finRotate_rev_finRotate, Equiv.apply_symm_apply]

/-- The successor in the reverse ring is the predecessor in the ring. -/
theorem rev_next_reverse (i : Fin P.n) : Fin.rev (P.reverse.next i) = P.prev (Fin.rev i) := by
  have h := finRotate_rev_finRotate i
  apply (finRotate P.n).injective
  change finRotate P.n (Fin.rev (finRotate P.n i)) = finRotate P.n ((finRotate P.n).symm (Fin.rev i))
  rw [h, Equiv.apply_symm_apply]

/-- Each edge of the reverse ring is an edge of the ring, reversed: the edge
sequence really is reversed, not only the vertex labels. -/
theorem reverse_edge (i : Fin P.n) :
    P.reverse.edge i = (P.edge (P.prev (Fin.rev i))).swap := by
  simp only [edge, Segment.swap, next_prev]
  congr 1
  exact congrArg P.vertex (P.rev_next_reverse i)

/-- A simple polygon: at least three vertices, no zero-length edge,
consecutive edges meeting only at their shared vertex, and every other pair of
edges disjoint. -/
structure IsSimple : Prop where
  three_le : 3 ≤ P.n
  edge_nondegenerate : ∀ i, (P.edge i).Nondegenerate
  adjacent_inter : ∀ i, (P.edge i).toSet ∩ (P.edge (P.next i)).toSet = {P.vertex (P.next i)}
  nonadjacent_disjoint : ∀ i j, i ≠ j → P.next i ≠ j → P.next j ≠ i →
    Disjoint (P.edge i).toSet (P.edge j).toSet

end RawPolygon

/-- A simple polygon. -/
def SimplePolygon : Type := {P : RawPolygon // P.IsSimple}

namespace Triangle

/-- A triangle as a ring of three vertices. -/
noncomputable def toPolygon (T : Triangle) : RawPolygon := ⟨3, ![T.a, T.b, T.c]⟩

@[simp] theorem finRotate_three_zero : finRotate 3 0 = 1 := by decide
@[simp] theorem finRotate_three_one : finRotate 3 1 = 2 := by decide
@[simp] theorem finRotate_three_two : finRotate 3 2 = 0 := by decide

/-- In a ring of three, any two distinct edges are consecutive. -/
theorem fin_three_adjacent :
    ∀ i j : Fin 3, i ≠ j → finRotate 3 i ≠ j → finRotate 3 j ≠ i → False := by
  decide

/-- A nondegenerate triangle is a simple polygon. -/
theorem isSimple_toPolygon {T : Triangle} (h : T.Nondegenerate) : T.toPolygon.IsSimple := by
  have h₁ : orient T.a T.b T.c ≠ 0 := h
  have h₂ : orient T.b T.c T.a ≠ 0 := by rwa [orient_rotate]
  have h₃ : orient T.c T.a T.b ≠ 0 := by rwa [orient_rotate, orient_rotate]
  have hne : ∀ {u v w : Point2D}, orient u v w ≠ 0 → u ≠ v := by
    rintro u v w huvw rfl; simp at huvw
  refine ⟨le_rfl, fun i => ?_, fun i => ?_, fun i j hij h₁ h₂ => ?_⟩
  · change Fin 3 at i
    fin_cases i <;> simp [RawPolygon.edge, RawPolygon.next, Segment.Nondegenerate, toPolygon]
    · exact hne h₁
    · exact hne h₂
    · exact hne h₃
  · change Fin 3 at i
    fin_cases i <;> simp only [RawPolygon.edge, RawPolygon.next, Segment.toSet, toPolygon] <;>
      simp
    · exact segment_inter_segment_eq h₁
    · exact segment_inter_segment_eq h₂
    · exact segment_inter_segment_eq h₃
  · exact (fin_three_adjacent i j hij h₁ h₂).elim

end Triangle

end ComputationalGeometry
