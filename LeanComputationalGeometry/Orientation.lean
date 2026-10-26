import LeanComputationalGeometry.Point
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Orientation

`cross u v = u.x * v.y - u.y * v.x` is the cross product of two plane
vectors, the signed area of the parallelogram they span. The orientation of
three points is

```
orient a b c = cross (b - a) (c - a)
             = (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x),
```

positive when `a, b, c` turn counterclockwise, negative when they turn
clockwise, zero when they are collinear. It is twice the signed area of the
triangle `a b c`.

The definitions are tied to Mathlib's rather than left standing alone:

- `orient_eq_det`: `orient` is the determinant of the 2×2 matrix with columns
  `b - a` and `c - a` (`Matrix.det`).
- `orient_eq_zero_iff_collinear`: it vanishes exactly when `{a, b, c}` is
  `Collinear` in Mathlib's sense.
- `orient_ne_zero_iff_affineIndependent`: it is nonzero exactly when the three
  points are affinely independent.

The algebra a computational geometry library leans on:

- swapping two arguments negates it (`orient_swap₁₂`, `orient_swap₂₃`,
  `orient_swap₁₃`), and a cyclic permutation keeps it (`orient_rotate`);
- it is invariant under translation (`orient_add_vec`);
- it is affine in each argument; for the last one, along the line from `p` to
  `q` it interpolates linearly (`orient_lineMap`);
- it is the triangle's shoelace sum (`orient_eq_cross_sum`), which the polygon
  signed area builds on.
-/

namespace ComputationalGeometry

open Point2D

/-! ## The cross product -/

/-- The cross product of two plane vectors. -/
def cross (u v : Point2D) : ℝ := u.x * v.y - u.y * v.x

theorem cross_comm (u v : Point2D) : cross v u = -cross u v := by
  unfold cross; ring

@[simp] theorem cross_self (u : Point2D) : cross u u = 0 := by
  unfold cross; ring

@[simp] theorem cross_zero_left (u : Point2D) : cross 0 u = 0 := by
  simp [cross]

@[simp] theorem cross_zero_right (u : Point2D) : cross u 0 = 0 := by
  simp [cross]

theorem cross_add_left (u v w : Point2D) : cross (u + v) w = cross u w + cross v w := by
  simp only [cross, x_add, y_add]; ring

theorem cross_add_right (u v w : Point2D) : cross u (v + w) = cross u v + cross u w := by
  simp only [cross, x_add, y_add]; ring

theorem cross_sub_left (u v w : Point2D) : cross (u - v) w = cross u w - cross v w := by
  simp only [cross, x_sub, y_sub]; ring

theorem cross_sub_right (u v w : Point2D) : cross u (v - w) = cross u v - cross u w := by
  simp only [cross, x_sub, y_sub]; ring

theorem cross_smul_left (c : ℝ) (u v : Point2D) : cross (c • u) v = c * cross u v := by
  simp only [cross, x_smul, y_smul]; ring

theorem cross_smul_right (c : ℝ) (u v : Point2D) : cross u (c • v) = c * cross u v := by
  simp only [cross, x_smul, y_smul]; ring

/-! ## Orientation of three points -/

/-- The orientation of `a, b, c`: twice the signed area of the triangle. -/
def orient (a b c : Point2D) : ℝ := cross (b - a) (c - a)

theorem orient_def (a b c : Point2D) :
    orient a b c = (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x) := rfl

/-- `orient` is a 2×2 determinant. -/
theorem orient_eq_det (a b c : Point2D) :
    orient a b c = !![b.x - a.x, c.x - a.x; b.y - a.y, c.y - a.y].det := by
  rw [Matrix.det_fin_two_of, orient_def]
  ring

/-- The triangle's shoelace sum. -/
theorem orient_eq_cross_sum (a b c : Point2D) :
    orient a b c = cross a b + cross b c + cross c a := by
  simp only [orient_def, cross]
  ring

theorem orient_swap₁₂ (a b c : Point2D) : orient b a c = -orient a b c := by
  simp only [orient_def]; ring

theorem orient_swap₂₃ (a b c : Point2D) : orient a c b = -orient a b c := by
  simp only [orient_def]; ring

theorem orient_swap₁₃ (a b c : Point2D) : orient c b a = -orient a b c := by
  simp only [orient_def]; ring

/-- A cyclic permutation keeps the orientation. -/
theorem orient_rotate (a b c : Point2D) : orient b c a = orient a b c := by
  simp only [orient_def]; ring

@[simp] theorem orient_self₁₂ (a c : Point2D) : orient a a c = 0 := by
  simp [orient]

@[simp] theorem orient_self₂₃ (a b : Point2D) : orient a b b = 0 := by
  simp [orient]

@[simp] theorem orient_self₁₃ (a b : Point2D) : orient a b a = 0 := by
  simp [orient]

/-- Translation keeps the orientation. -/
theorem orient_add_vec (a b c v : Point2D) : orient (a + v) (b + v) (c + v) = orient a b c := by
  simp only [orient_def, x_add, y_add]; ring

/-- Along the line from `p` to `q`, the orientation interpolates linearly. -/
theorem orient_lineMap (a b p q : Point2D) (t : ℝ) :
    orient a b ((1 - t) • p + t • q) = (1 - t) * orient a b p + t * orient a b q := by
  simp only [orient_def, x_add, y_add, x_smul, y_smul]; ring

/-- The same in the first argument. -/
theorem orient_lineMap₁ (p q b c : Point2D) (t : ℝ) :
    orient ((1 - t) • p + t • q) b c = (1 - t) * orient p b c + t * orient q b c := by
  simp only [orient_def, x_add, y_add, x_smul, y_smul]; ring

/-- The orientation is continuous in the last point. -/
@[fun_prop] theorem continuous_orient (a b : Point2D) : Continuous fun p => orient a b p := by
  simp only [orient_def]
  fun_prop

/-- Moving `p` by `w` changes the orientation by `cross (b - a) w`. -/
theorem orient_add (a b p w : Point2D) : orient a b (p + w) = orient a b p + cross (b - a) w := by
  simp only [orient_def, cross, x_add, y_add, x_sub, y_sub]
  ring

/-! ## Collinearity -/

/-- If the cross product of `u ≠ 0` with `w` vanishes, `w` is a multiple of
`u`. -/
theorem exists_smul_of_cross_eq_zero {u w : Point2D} (hu : u ≠ 0) (h : cross u w = 0) :
    ∃ t : ℝ, w = t • u := by
  unfold cross at h
  by_cases hx : u.x = 0
  · have hy : u.y ≠ 0 := fun hy => hu (Point2D.ext (by simp [hx]) (by simp [hy]))
    refine ⟨w.y / u.y, Point2D.ext ?_ ?_⟩
    · simp only [x_smul, hx, mul_zero]
      rw [hx, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero] at h
      exact h.resolve_left hy
    · simp only [y_smul]; field_simp
  · refine ⟨w.x / u.x, Point2D.ext ?_ ?_⟩
    · simp only [x_smul]; field_simp
    · simp only [y_smul]; field_simp; linarith

/-- `orient a b c = 0` exactly when the three points are collinear. -/
theorem orient_eq_zero_iff_collinear (a b c : Point2D) :
    orient a b c = 0 ↔ Collinear ℝ {a, b, c} := by
  rw [collinear_iff_of_mem (p₀ := a) (by simp)]
  constructor
  · intro h
    by_cases hab : b - a = 0
    · obtain ⟨v, hv⟩ : ∃ v : Point2D, c = v + a := ⟨c - a, by abel⟩
      refine ⟨v, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro p (rfl | rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨0, by rw [sub_eq_zero] at hab; simp [hab]⟩
      · exact ⟨1, by simp [hv]⟩
    · obtain ⟨t, ht⟩ := exists_smul_of_cross_eq_zero hab h
      refine ⟨b - a, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro p (rfl | rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨t, by rw [vadd_eq_add, ← ht]; abel⟩
  · rintro ⟨v, hv⟩
    obtain ⟨r, hr⟩ := hv b (by simp)
    obtain ⟨s, hs⟩ := hv c (by simp)
    rw [vadd_eq_add] at hr hs
    have hb : b - a = r • v := by rw [hr]; abel
    have hc : c - a = s • v := by rw [hs]; abel
    rw [orient, hb, hc, cross_smul_left, cross_smul_right, cross_self, mul_zero, mul_zero]

/-- `orient a b c ≠ 0` exactly when the three points are affinely
independent. -/
theorem orient_ne_zero_iff_affineIndependent (a b c : Point2D) :
    orient a b c ≠ 0 ↔ AffineIndependent ℝ ![a, b, c] := by
  rw [affineIndependent_iff_not_collinear_set, ne_eq, orient_eq_zero_iff_collinear]

end ComputationalGeometry
