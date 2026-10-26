import LeanComputationalGeometry.Polygon.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Signed area: the shoelace formula

`signedArea2 P` is the shoelace sum `∑ cross (vertex i) (vertex (next i))`
over the edges of a ring, twice the signed area it encloses when it is
simple; `signedArea` is half of it. The definition makes sense for any raw
ring; what it measures for a non-simple one is a question for region
semantics, later.

- It does not depend on where the ring is placed (`signedArea2_translate`) or
  where it starts (`signedArea2_rotate`).
- For a triangle it is the triangle's signed double area, the orientation of
  its vertices (`Triangle.signedArea2_toPolygon`).

LeanGeospatial has its own small shoelace (`cross`, `signedArea2`,
`polygonArea`, and the area of a rectangle). This file is independent of it:
computing geometry is this library's job, and LeanGeospatial does not compute
geometry. LeanGeospatial may later use this as the canonical implementation;
that refactor is not part of this library's first release.
-/

namespace ComputationalGeometry

namespace RawPolygon

variable (P : RawPolygon)

/-- Twice the signed area: the shoelace sum over the edges. -/
def signedArea2 : ℝ := ∑ i, cross (P.vertex i) (P.vertex (P.next i))

/-- The signed area. -/
noncomputable def signedArea : ℝ := P.signedArea2 / 2

/-- The ring turns counterclockwise. -/
def IsCCW : Prop := 0 < P.signedArea2

/-- The ring turns clockwise. -/
def IsCW : Prop := P.signedArea2 < 0

/-- Traversing the ring the other way negates its signed area. -/
theorem signedArea2_reverse : P.reverse.signedArea2 = -P.signedArea2 := by
  show ∑ i : Fin P.n, cross (P.vertex (Fin.rev i)) (P.vertex (Fin.rev (finRotate P.n i))) = _
  simp only [rev_finRotate]
  have hrev := Equiv.sum_comp Fin.revPerm
    (fun j => cross (P.vertex j) (P.vertex ((finRotate P.n).symm j)))
  simp only [Fin.revPerm_apply] at hrev
  rw [hrev]
  rw [← Equiv.sum_comp (finRotate P.n)
    (fun j => cross (P.vertex j) (P.vertex ((finRotate P.n).symm j)))]
  simp only [Equiv.symm_apply_apply, signedArea2, next]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => cross_comm _ _

theorem isCCW_reverse_iff : P.reverse.IsCCW ↔ P.IsCW := by
  rw [IsCCW, IsCW, signedArea2_reverse, neg_pos]

theorem isCW_reverse_iff : P.reverse.IsCW ↔ P.IsCCW := by
  rw [IsCCW, IsCW, signedArea2_reverse, neg_lt_zero]

/-- Moving the ring does not change its signed area. -/
theorem signedArea2_translate (v : Point2D) : (P.translate v).signedArea2 = P.signedArea2 := by
  show ∑ i : Fin P.n, cross (P.vertex i + v) (P.vertex (finRotate P.n i) + v) =
    ∑ i : Fin P.n, cross (P.vertex i) (P.vertex (finRotate P.n i))
  simp only [cross_add_left, cross_add_right, cross_self, add_zero]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hshift : ∑ i, cross v (P.vertex (finRotate P.n i)) = ∑ i, cross v (P.vertex i) :=
    Equiv.sum_comp (finRotate P.n) (fun i => cross v (P.vertex i))
  have hcancel : ∑ i, cross (P.vertex i) v + ∑ i, cross v (P.vertex i) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by rw [cross_comm (P.vertex i) v]; ring
  rw [hshift]
  linarith [hcancel]

/-- Starting the ring one vertex later does not change its signed area. -/
theorem signedArea2_rotate : P.rotate.signedArea2 = P.signedArea2 :=
  Equiv.sum_comp (finRotate P.n) (fun i => cross (P.vertex i) (P.vertex (finRotate P.n i)))

end RawPolygon

/-- For a triangle the shoelace sum is the orientation of the vertices. -/
theorem Triangle.signedArea2_toPolygon (T : Triangle) :
    T.toPolygon.signedArea2 = T.signedArea2 := by
  rw [T.signedArea2_eq_cross_sum]
  show ∑ i : Fin 3, cross (![T.a, T.b, T.c] i) (![T.a, T.b, T.c] (finRotate 3 i)) = _
  rw [Fin.sum_univ_three]
  simp

end ComputationalGeometry
