import LeanComputationalGeometry.Polygon.Region
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Signed area as the integral of the winding number

For any ring, the winding number integrated over the plane is half the
shoelace sum (`integral_integral_windingNumber`), computed here with
iterated one-dimensional interval integrals. Along a horizontal line at
height `y`, an edge contributes `sgn * [x < crossX]`, where `crossX` is where
the edge crosses the line, so its integral in `x` is
`sgn * (crossX - X₀)`; integrated in `y`, that is the edge's trapezoid
`(b.y - a.y) * ((a.x + b.x) / 2 - X₀)`, and the trapezoids add up to half the
shoelace sum.

Consequently a ring whose winding numbers off the boundary are all
nonnegative has a nonnegative shoelace sum
(`signedArea2_nonneg_of_windingNumber_nonneg`).
-/

namespace ComputationalGeometry

open Set Point2D MeasureTheory

open Classical in
/-- The sign with which the edge from `a` to `b` crosses the height `y`,
following the half-open rule of `edgeContribution`. -/
noncomputable def crossSign (a b : Point2D) (y : ℝ) : ℝ :=
  if a.y ≤ y ∧ y < b.y then 1 else if b.y ≤ y ∧ y < a.y then -1 else 0

/-- Where the line of the edge from `a` to `b` crosses the height `y`. -/
noncomputable def crossX (a b : Point2D) (y : ℝ) : ℝ :=
  a.x + (b.x - a.x) * (y - a.y) / (b.y - a.y)

theorem orient_mk_eq {a b : Point2D} (hab : a.y ≠ b.y) (x y : ℝ) :
    orient a b (mk x y) = (b.y - a.y) * (crossX a b y - x) := by
  have : b.y - a.y ≠ 0 := sub_ne_zero.mpr hab.symm
  simp only [crossX, orient_def, x_mk, y_mk]
  field_simp
  ring

open Classical in
/-- An edge's contribution at `(x, y)`: its crossing sign, if it crosses to the
right of `x`. -/
theorem edgeContribution_mk (a b : Point2D) (x y : ℝ) :
    (edgeContribution (mk x y) a b : ℝ) =
      crossSign a b y * (if x < crossX a b y then 1 else 0) := by
  by_cases hu : a.y ≤ y ∧ y < b.y
  · have hab : a.y ≠ b.y := by linarith [hu.1, hu.2]
    have hpos : 0 < b.y - a.y := by linarith [hu.1, hu.2]
    rw [edgeContribution_of_up (by simpa using hu.1) (by simpa using hu.2), orient_mk_eq hab]
    simp only [crossSign, hu, and_self, ↓reduceIte, one_mul]
    by_cases hx : x < crossX a b y
    · simp [hx, mul_pos hpos (sub_pos.mpr hx)]
    · simp [hx, mul_nonpos_of_nonneg_of_nonpos hpos.le (sub_nonpos.mpr (not_lt.mp hx))]
  by_cases hd : b.y ≤ y ∧ y < a.y
  · have hab : a.y ≠ b.y := by linarith [hd.1, hd.2]
    have hneg : b.y - a.y < 0 := by linarith [hd.1, hd.2]
    rw [edgeContribution_of_down (by simpa using hd.2) (by simpa using hd.1), orient_mk_eq hab]
    simp only [crossSign, hu, hd, and_self, ↓reduceIte]
    by_cases hx : x < crossX a b y
    · simp [hx, mul_neg_of_neg_of_pos hneg (sub_pos.mpr hx)]
    · simp [hx, mul_nonneg_of_nonpos_of_nonpos hneg.le (sub_nonpos.mpr (not_lt.mp hx))]
  · have : edgeContribution (mk x y) a b = 0 := by
      by_cases ha : a.y ≤ y
      · have hb : b.y ≤ y := not_lt.mp fun h => hu ⟨ha, h⟩
        exact edgeContribution_of_below (by simpa using ha) (by simpa using hb)
      · have hb : y < b.y := not_le.mp fun h => hd ⟨h, not_le.mp ha⟩
        exact edgeContribution_of_above (by simpa using not_le.mp ha) (by simpa using hb)
    simp [this, crossSign, hu, hd]

/-! ## Along a horizontal line -/

/-- Where an edge crosses a height it counts at, it crosses between its ends. -/
theorem crossX_mem {a b : Point2D} {y : ℝ} (h : crossSign a b y ≠ 0) :
    min a.x b.x ≤ crossX a b y ∧ crossX a b y ≤ max a.x b.x := by
  have hrange : (a.y ≤ y ∧ y < b.y) ∨ (b.y ≤ y ∧ y < a.y) := by
    by_contra hc
    simp only [not_or] at hc
    exact h (by simp [crossSign, hc.1, hc.2])
  have hab : a.y ≠ b.y := by rcases hrange with h | h <;> linarith [h.1, h.2]
  have hd : b.y - a.y ≠ 0 := sub_ne_zero.mpr hab.symm
  set t := (y - a.y) / (b.y - a.y)
  have ht : 0 ≤ t ∧ t ≤ 1 := by
    rcases hrange with h | h
    · have hpos : 0 < b.y - a.y := by linarith [h.1, h.2]
      exact ⟨div_nonneg (by linarith [h.1]) hpos.le, (div_le_one hpos).mpr (by linarith [h.2])⟩
    · have hneg : b.y - a.y < 0 := by linarith [h.1, h.2]
      exact ⟨div_nonneg_of_nonpos (by linarith [h.2]) hneg.le,
        (div_le_one_of_neg hneg).mpr (by linarith [h.1])⟩
  have hc : crossX a b y = (1 - t) * a.x + t * b.x := by
    simp only [crossX, t]; field_simp; ring
  rw [hc]
  constructor
  · nlinarith [min_le_left a.x b.x, min_le_right a.x b.x, mul_nonneg (sub_nonneg.mpr ht.2)
      (sub_nonneg.mpr (min_le_left a.x b.x)), mul_nonneg ht.1 (sub_nonneg.mpr (min_le_right a.x b.x))]
  · nlinarith [le_max_left a.x b.x, le_max_right a.x b.x, mul_nonneg (sub_nonneg.mpr ht.2)
      (sub_nonneg.mpr (le_max_left a.x b.x)), mul_nonneg ht.1 (sub_nonneg.mpr (le_max_right a.x b.x))]

theorem integral_step {X₀ X₁ c : ℝ} (h₀ : X₀ ≤ c) (h₁ : c ≤ X₁) :
    ∫ x in X₀..X₁, (if x < c then (1 : ℝ) else 0) = c - X₀ := by
  classical
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ uIoc X₀ X₁ →
      (if x < c then (1 : ℝ) else 0) = {x | x ≤ c}.indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [Measure.ae_ne volume c] with x hx _
    by_cases hlt : x < c
    · simp [hlt, hlt.le]
    · have : ¬ x ≤ c := fun h => hlt (lt_of_le_of_ne h hx)
      simp [hlt, this]
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_indicator ⟨h₀, h₁⟩,
    intervalIntegral.integral_const, smul_eq_mul, mul_one]

/-- Integrated across a horizontal line, an edge gives its crossing sign times
the distance from the line's left end to the crossing. -/
theorem integral_edgeContribution_mk (a b : Point2D) (y : ℝ) {X₀ X₁ : ℝ}
    (h₀ : X₀ ≤ min a.x b.x) (h₁ : max a.x b.x ≤ X₁) :
    ∫ x in X₀..X₁, (edgeContribution (mk x y) a b : ℝ) = crossSign a b y * (crossX a b y - X₀) := by
  classical
  simp_rw [edgeContribution_mk]
  rw [intervalIntegral.integral_const_mul]
  by_cases hs : crossSign a b y = 0
  · simp [hs]
  · obtain ⟨hc₀, hc₁⟩ := crossX_mem hs
    rw [integral_step (h₀.trans hc₀) (hc₁.trans h₁)]

theorem intervalIntegrable_edgeContribution_mk (a b : Point2D) (y X₀ X₁ : ℝ) :
    IntervalIntegrable (fun x => (edgeContribution (mk x y) a b : ℝ)) volume X₀ X₁ := by
  classical
  simp_rw [edgeContribution_mk]
  refine IntervalIntegrable.const_mul ?_ _
  apply Antitone.intervalIntegrable
  intro x x' hxx'
  by_cases h : x' < crossX a b y
  · simp [h, lt_of_le_of_lt hxx' h]
  · by_cases h' : x < crossX a b y <;> simp [h, h']

/-! ## Across the heights -/

theorem integral_crossX {a b : Point2D} (hab : a.y ≠ b.y) (X₀ : ℝ) :
    ∫ y in a.y..b.y, (crossX a b y - X₀) = (b.y - a.y) * ((a.x + b.x) / 2 - X₀) := by
  have hd : b.y - a.y ≠ 0 := sub_ne_zero.mpr hab.symm
  have hf : (fun y => crossX a b y - X₀) =
      fun y => (a.x - X₀ - (b.x - a.x) / (b.y - a.y) * a.y) + (b.x - a.x) / (b.y - a.y) * y := by
    funext y; simp only [crossX]; field_simp; ring
  rw [hf, intervalIntegral.integral_add intervalIntegrable_const
    ((by fun_prop : Continuous fun y : ℝ => (b.x - a.x) / (b.y - a.y) * y).intervalIntegrable _ _),
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id, smul_eq_mul]
  field_simp
  ring

theorem integral_indicator_Ico {f : ℝ → ℝ} {Y₀ Y₁ α β : ℝ} (h₀ : Y₀ < α) (hαβ : α ≤ β)
    (h₁ : β ≤ Y₁) :
    ∫ y in Y₀..Y₁, (Ico α β).indicator f y = ∫ y in α..β, f y := by
  have hset : Ioc Y₀ Y₁ ∩ Ico α β = Ico α β := by
    ext y
    simp only [mem_inter_iff, mem_Ioc, mem_Ico]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro ⟨h₁', h₂'⟩; exact ⟨⟨by linarith, by linarith⟩, h₁', h₂'⟩
  rw [intervalIntegral.integral_of_le (by linarith), setIntegral_indicator measurableSet_Ico, hset,
    intervalIntegral.integral_of_le hαβ, integral_Ico_eq_integral_Ioc]

theorem crossSign_mul_eq (a b : Point2D) (X₀ y : ℝ) :
    crossSign a b y * (crossX a b y - X₀) =
      (Ico a.y b.y).indicator (fun y => crossX a b y - X₀) y -
        (Ico b.y a.y).indicator (fun y => crossX a b y - X₀) y := by
  classical
  by_cases hu : a.y ≤ y ∧ y < b.y
  · have : ¬ (b.y ≤ y ∧ y < a.y) := fun h => by linarith [h.1, h.2, hu.1, hu.2]
    simp [crossSign, hu, indicator, mem_Ico, this]
  · by_cases hd : b.y ≤ y ∧ y < a.y
    · simp [crossSign, hu, hd, indicator, mem_Ico]
    · simp [crossSign, hu, hd, indicator, mem_Ico]

/-- Integrated over the heights, the crossings of an edge give its trapezoid
down to the vertical line `x = X₀`. -/
theorem integral_crossSign (a b : Point2D) {Y₀ Y₁ : ℝ} (X₀ : ℝ) (h₀ : Y₀ < min a.y b.y)
    (h₁ : max a.y b.y ≤ Y₁) :
    ∫ y in Y₀..Y₁, crossSign a b y * (crossX a b y - X₀) = (b.y - a.y) * ((a.x + b.x) / 2 - X₀) := by
  have hc : Continuous fun y => crossX a b y - X₀ := by unfold crossX; fun_prop
  have hint : ∀ α β : ℝ, IntervalIntegrable ((Ico α β).indicator fun y => crossX a b y - X₀)
      volume Y₀ Y₁ := fun α β =>
    intervalIntegrable_iff.mpr ((intervalIntegrable_iff.mp (hc.intervalIntegrable Y₀ Y₁)).indicator
      measurableSet_Ico)
  simp_rw [crossSign_mul_eq]
  rw [intervalIntegral.integral_sub (hint _ _) (hint _ _)]
  rcases lt_trichotomy a.y b.y with hab | hab | hab
  · rw [integral_indicator_Ico (lt_of_lt_of_le h₀ (min_le_left _ _)) hab.le
      ((le_max_right _ _).trans h₁), integral_crossX hab.ne]
    have : Ico b.y a.y = ∅ := Ico_eq_empty (not_lt.mpr hab.le)
    simp [this]
  · have h₁' : Ico a.y b.y = ∅ := by simp [hab]
    have h₂' : Ico b.y a.y = ∅ := by simp [hab]
    simp [hab]
  · rw [integral_indicator_Ico (lt_of_lt_of_le h₀ (min_le_right _ _)) hab.le
      ((le_max_left _ _).trans h₁)]
    have : Ico a.y b.y = ∅ := Ico_eq_empty (not_lt.mpr hab.le)
    simp only [this, indicator_empty, intervalIntegral.integral_zero, zero_sub]
    rw [← intervalIntegral.integral_symm, integral_crossX hab.ne']

theorem intervalIntegrable_crossSign (a b : Point2D) (X₀ Y₀ Y₁ : ℝ) :
    IntervalIntegrable (fun y => crossSign a b y * (crossX a b y - X₀)) volume Y₀ Y₁ := by
  have hc : Continuous fun y => crossX a b y - X₀ := by unfold crossX; fun_prop
  have hint : ∀ α β : ℝ, IntervalIntegrable ((Ico α β).indicator fun y => crossX a b y - X₀)
      volume Y₀ Y₁ := fun α β =>
    intervalIntegrable_iff.mpr ((intervalIntegrable_iff.mp (hc.intervalIntegrable Y₀ Y₁)).indicator
      measurableSet_Ico)
  simp_rw [crossSign_mul_eq]
  exact (hint _ _).sub (hint _ _)

/-! ## The whole ring -/

namespace RawPolygon

variable (P : RawPolygon)

theorem windingNumber_cast (p : Point2D) :
    (P.windingNumber p : ℝ) = ∑ i, (edgeContribution p (P.vertex i) (P.vertex (P.next i)) : ℝ) := by
  simp [windingNumber]

theorem sum_dy : ∑ i, ((P.vertex (P.next i)).y - (P.vertex i).y) = 0 := by
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  exact Equiv.sum_comp (finRotate P.n) (fun i => (P.vertex i).y)

theorem sum_trapezoid :
    ∑ i, ((P.vertex (P.next i)).y - (P.vertex i).y) * ((P.vertex i).x + (P.vertex (P.next i)).x) =
      P.signedArea2 := by
  have hshift : ∑ i, (P.vertex (P.next i)).x * (P.vertex (P.next i)).y =
      ∑ i, (P.vertex i).x * (P.vertex i).y :=
    Equiv.sum_comp (finRotate P.n) (fun i => (P.vertex i).x * (P.vertex i).y)
  have : ∀ i, ((P.vertex (P.next i)).y - (P.vertex i).y) * ((P.vertex i).x + (P.vertex (P.next i)).x) =
      cross (P.vertex i) (P.vertex (P.next i)) +
        ((P.vertex (P.next i)).x * (P.vertex (P.next i)).y - (P.vertex i).x * (P.vertex i).y) := by
    intro i; simp only [cross]; ring
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, Finset.sum_sub_distrib, hshift,
    sub_self, add_zero]
  rfl

/-- Half the shoelace sum is the winding number integrated over a square
containing the ring. -/
theorem signedArea2_eq_integral {M : ℝ} (hM : ∀ i, |(P.vertex i).x| < M ∧ |(P.vertex i).y| < M) :
    P.signedArea2 = 2 * ∫ y in -M..M, ∫ x in -M..M, (P.windingNumber (Point2D.mk x y) : ℝ) := by
  have bx : ∀ i, -M < (P.vertex i).x ∧ (P.vertex i).x < M := fun i =>
    ⟨by linarith [neg_abs_le (P.vertex i).x, (hM i).1], by linarith [le_abs_self (P.vertex i).x, (hM i).1]⟩
  have hy : ∀ i, -M < (P.vertex i).y ∧ (P.vertex i).y < M := fun i =>
    ⟨by linarith [neg_abs_le (P.vertex i).y, (hM i).2], by linarith [le_abs_self (P.vertex i).y, (hM i).2]⟩
  have hinner : ∀ y, ∫ x in -M..M, (P.windingNumber (Point2D.mk x y) : ℝ) =
      ∑ i, crossSign (P.vertex i) (P.vertex (P.next i)) y *
        (crossX (P.vertex i) (P.vertex (P.next i)) y - -M) := by
    intro y
    simp_rw [windingNumber_cast]
    rw [intervalIntegral.integral_finsetSum fun i _ =>
      intervalIntegrable_edgeContribution_mk _ _ y _ _]
    refine Finset.sum_congr rfl fun i _ => integral_edgeContribution_mk _ _ y ?_ ?_
    · exact le_min (bx i).1.le (bx (P.next i)).1.le
    · exact max_le (bx i).2.le (bx (P.next i)).2.le
  simp_rw [hinner]
  rw [intervalIntegral.integral_finsetSum fun i _ => intervalIntegrable_crossSign _ _ _ _ _]
  rw [Finset.sum_congr rfl fun i _ => integral_crossSign (P.vertex i) (P.vertex (P.next i)) (-M)
    (lt_min (hy i).1 (hy (P.next i)).1) (max_le (hy i).2.le (hy (P.next i)).2.le)]
  have h₁ := P.sum_dy
  have h₂ := P.sum_trapezoid
  have : ∑ i, ((P.vertex (P.next i)).y - (P.vertex i).y) *
      (((P.vertex i).x + (P.vertex (P.next i)).x) / 2 - -M) =
      (∑ i, ((P.vertex (P.next i)).y - (P.vertex i).y) * ((P.vertex i).x + (P.vertex (P.next i)).x)) / 2 +
        M * ∑ i, ((P.vertex (P.next i)).y - (P.vertex i).y) := by
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, h₁, h₂]
  ring

/-- A ring whose winding numbers off the boundary are all nonnegative has a
nonnegative shoelace sum. -/
theorem signedArea2_nonneg_of_windingNumber_nonneg
    (h : ∀ p, ¬ P.OnBoundary p → 0 ≤ P.windingNumber p) : 0 ≤ P.signedArea2 := by
  set M := 1 + ∑ i, (|(P.vertex i).x| + |(P.vertex i).y|)
  have hM : ∀ i, |(P.vertex i).x| < M ∧ |(P.vertex i).y| < M := by
    intro i
    have := Finset.single_le_sum (f := fun i => |(P.vertex i).x| + |(P.vertex i).y|)
      (fun _ _ => by positivity) (Finset.mem_univ i)
    constructor <;> linarith [abs_nonneg (P.vertex i).x, abs_nonneg (P.vertex i).y]
  have hM0 : 0 < M := by
    have : 0 ≤ ∑ i, (|(P.vertex i).x| + |(P.vertex i).y|) := Finset.sum_nonneg fun _ _ => by positivity
    linarith
  rw [P.signedArea2_eq_integral hM]
  refine mul_nonneg two_pos.le (intervalIntegral.integral_nonneg_of_ae (by linarith) ?_)
  -- Off the vertices' heights, each line meets the boundary at finitely many points.
  have hfin : (Finset.univ.image fun i => (P.vertex i).y : Set ℝ).Finite := Finset.finite_toSet _
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero volume)] with y hy
  refine intervalIntegral.integral_nonneg_of_ae (by linarith) ?_
  have hfinx : (Finset.univ.image fun i => crossX (P.vertex i) (P.vertex (P.next i)) y : Set ℝ).Finite :=
    Finset.finite_toSet _
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hfinx.measure_zero volume)] with x hx
  have hb : ¬ P.OnBoundary (Point2D.mk x y) := by
    rintro ⟨i, hi⟩
    apply hx
    simp only [Finset.coe_image, Finset.coe_univ, image_univ, mem_range]
    refine ⟨i, ?_⟩
    have hya : (P.vertex i).y ≠ y := fun e => hy (by simp [← e])
    have hyb : (P.vertex (P.next i)).y ≠ y := fun e => hy (by simp [← e])
    have hab : (P.vertex i).y ≠ (P.vertex (P.next i)).y := by
      intro e
      obtain ⟨t, -, htq⟩ := (Segment.mem_toSet_iff_exists _).mp hi
      have := congrArg Point2D.y htq
      simp only [y_add, y_smul] at this
      change (1 - t) * (P.vertex i).y + t * (P.vertex (P.next i)).y = y at this
      rw [← e] at this
      exact hya (by linarith)
    have h0 := Segment.orient_eq_zero_of_mem _ hi
    change orient (P.vertex i) (P.vertex (P.next i)) (Point2D.mk x y) = 0 at h0
    rw [orient_mk_eq hab] at h0
    have hd : (P.vertex (P.next i)).y - (P.vertex i).y ≠ 0 := sub_ne_zero.mpr hab.symm
    have := (mul_eq_zero.mp h0).resolve_left hd
    linarith
  show (0 : ℝ) ≤ _
  exact_mod_cast h _ hb

end RawPolygon

end ComputationalGeometry
