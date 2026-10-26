import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Points in the plane

The plane is Mathlib's Euclidean plane `EuclideanSpace ℝ (Fin 2)`, the same
type that LeanGeodesy calls `Geodesy.E2` and LeanGeospatial calls
`Geospatial.Point2D`. `Point2D` here is a reducible abbreviation of it, not a
new type, so a point produced in either sibling library is a point here with
no conversion.

`Point2D.x` and `Point2D.y` read the coordinates and `Point2D.mk x y` builds a
point. Addition, subtraction and scalar multiplication are those of the
Euclidean space and act coordinatewise (`x_add`, `x_sub`, `x_smul`, ...).
-/

namespace ComputationalGeometry

/-- A point of the plane: Mathlib's `EuclideanSpace ℝ (Fin 2)`. -/
abbrev Point2D := EuclideanSpace ℝ (Fin 2)

example : Point2D = EuclideanSpace ℝ (Fin 2) := by with_reducible rfl

namespace Point2D

/-- The point with coordinates `(x, y)`. -/
noncomputable def mk (x y : ℝ) : Point2D := !₂[x, y]

/-- The first coordinate. -/
def x (p : Point2D) : ℝ := p 0

/-- The second coordinate. -/
def y (p : Point2D) : ℝ := p 1

@[simp] theorem x_mk (x y : ℝ) : (mk x y).x = x := rfl
@[simp] theorem y_mk (x y : ℝ) : (mk x y).y = y := rfl

@[simp] theorem x_add (p q : Point2D) : (p + q).x = p.x + q.x := rfl
@[simp] theorem y_add (p q : Point2D) : (p + q).y = p.y + q.y := rfl
@[simp] theorem x_sub (p q : Point2D) : (p - q).x = p.x - q.x := rfl
@[simp] theorem y_sub (p q : Point2D) : (p - q).y = p.y - q.y := rfl
@[simp] theorem x_neg (p : Point2D) : (-p).x = -p.x := rfl
@[simp] theorem y_neg (p : Point2D) : (-p).y = -p.y := rfl
@[simp] theorem x_smul (c : ℝ) (p : Point2D) : (c • p).x = c * p.x := rfl
@[simp] theorem y_smul (c : ℝ) (p : Point2D) : (c • p).y = c * p.y := rfl
@[simp] theorem x_zero : (0 : Point2D).x = 0 := rfl
@[simp] theorem y_zero : (0 : Point2D).y = 0 := rfl

/-- A point is determined by its coordinates. -/
@[ext] theorem ext {p q : Point2D} (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  ext i
  fin_cases i
  · exact hx
  · exact hy

theorem ext_iff' {p q : Point2D} : p = q ↔ p.x = q.x ∧ p.y = q.y :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨hx, hy⟩ => ext hx hy⟩

@[simp] theorem mk_x_y (p : Point2D) : mk p.x p.y = p := ext rfl rfl

end Point2D

end ComputationalGeometry
