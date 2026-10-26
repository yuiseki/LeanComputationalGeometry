import LeanComputationalGeometry.Orientation
import Mathlib.Analysis.Convex.Segment
import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Segments and their intersection

A `Segment` is a pair of endpoints `p, q`, possibly equal. Its point set is
Mathlib's closed `segment ℝ p q` (`Segment.toSet`), and its relative interior
is Mathlib's `openSegment ℝ p q` (`Segment.relInterior`), which for a
degenerate segment is the single point.

Intersection is stated three ways, and each theorem says which cases it
covers.

| Notion | Meaning |
| --- | --- |
| `Intersects s t` | the closed segments share a point, endpoints included |
| `ProperlyIntersect s t` | the lines are not parallel and the open segments meet |
| `GeneralPosition s t` | no endpoint lies on the other segment's line |

The orientation tests that decide them:

| Test | Meaning |
| --- | --- |
| `Straddles s t` | `t`'s endpoints lie strictly on opposite sides of `s`'s line |
| `CrossTest s t` | `Straddles s t ∧ Straddles t s` |
| `IntersectTest s t` | `CrossTest s t`, or an endpoint of one lies on the other |

The theorems:

- `properlyIntersect_iff_crossTest`, with no assumption: the strict test
  decides proper intersection exactly. The crossing point is
  `crossingPoint`, in both open segments.
- `intersects_iff_crossTest_of_generalPosition`: in general position touching
  is impossible, and the strict test alone decides intersection.
- `intersects_iff_intersectTest`, with no assumption: the classical test
  decides intersection in every case, endpoint touching and collinear overlap
  included.
- `mem_toSet_iff`: a point is on a segment exactly when it is collinear with
  the endpoints and each coordinate lies between theirs, which makes the
  endpoint checks of `IntersectTest` computable.
-/

namespace ComputationalGeometry

open Set Point2D

/-- A segment of the plane, given by its endpoints, which may coincide. -/
structure Segment where
  /-- The first endpoint. -/
  p : Point2D
  /-- The second endpoint. -/
  q : Point2D

namespace Segment

variable (s : Segment)

/-- The closed segment. -/
def toSet : Set Point2D := segment ℝ s.p s.q

/-- The relative interior: the open segment. A degenerate segment's is its
single point. -/
def relInterior : Set Point2D := openSegment ℝ s.p s.q

/-- The endpoints differ. -/
def Nondegenerate : Prop := s.p ≠ s.q

/-- The vector from the first endpoint to the second. -/
def direction : Point2D := s.q - s.p

/-- The same segment, traversed the other way. -/
def swap : Segment := ⟨s.q, s.p⟩

theorem toSet_swap : s.swap.toSet = s.toSet := segment_symm ℝ s.q s.p

theorem p_mem_toSet : s.p ∈ s.toSet := left_mem_segment ℝ s.p s.q

theorem q_mem_toSet : s.q ∈ s.toSet := right_mem_segment ℝ s.p s.q

theorem relInterior_subset_toSet : s.relInterior ⊆ s.toSet := openSegment_subset_segment ℝ _ _

theorem mem_toSet_iff_exists {x : Point2D} :
    x ∈ s.toSet ↔ ∃ t ∈ Icc (0 : ℝ) 1, (1 - t) • s.p + t • s.q = x := by
  rw [toSet, segment_eq_image]
  rfl

theorem mem_relInterior_iff_exists {x : Point2D} :
    x ∈ s.relInterior ↔ ∃ t ∈ Ioo (0 : ℝ) 1, (1 - t) • s.p + t • s.q = x := by
  rw [relInterior, openSegment_eq_image]
  rfl

/-- A point of the segment is on its line. -/
theorem orient_eq_zero_of_mem {x : Point2D} (hx : x ∈ s.toSet) : orient s.p s.q x = 0 := by
  obtain ⟨t, -, rfl⟩ := s.mem_toSet_iff_exists.mp hx
  rw [orient_lineMap]
  simp

end Segment

/-! ## Notions and tests -/

/-- The closed segments share a point, endpoints included. -/
def Intersects (s t : Segment) : Prop := (s.toSet ∩ t.toSet).Nonempty

/-- The lines are not parallel and the open segments meet: the segments cross
at one point inside both. -/
def ProperlyIntersect (s t : Segment) : Prop :=
  cross s.direction t.direction ≠ 0 ∧ (s.relInterior ∩ t.relInterior).Nonempty

/-- No endpoint lies on the other segment's line. -/
def GeneralPosition (s t : Segment) : Prop :=
  orient s.p s.q t.p ≠ 0 ∧ orient s.p s.q t.q ≠ 0 ∧ orient t.p t.q s.p ≠ 0 ∧
    orient t.p t.q s.q ≠ 0

/-- `t`'s endpoints lie strictly on opposite sides of `s`'s line. -/
def Straddles (s t : Segment) : Prop := orient s.p s.q t.p * orient s.p s.q t.q < 0

/-- The strict orientation test. -/
def CrossTest (s t : Segment) : Prop := Straddles s t ∧ Straddles t s

/-- The classical segment intersection test. -/
def IntersectTest (s t : Segment) : Prop :=
  CrossTest s t ∨ t.p ∈ s.toSet ∨ t.q ∈ s.toSet ∨ s.p ∈ t.toSet ∨ s.q ∈ t.toSet

theorem intersects_comm {s t : Segment} : Intersects s t ↔ Intersects t s := by
  unfold Intersects
  rw [inter_comm]

theorem generalPosition_comm {s t : Segment} : GeneralPosition s t ↔ GeneralPosition t s := by
  unfold GeneralPosition
  tauto

/-! ## Scalar facts -/

/-- If `(1 - t) d₁ + t d₂ = 0` with `0 < t < 1` and not both values zero,
they have opposite signs. -/
theorem mul_neg_of_interpolate_eq_zero {d₁ d₂ t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1)
    (h : (1 - t) * d₁ + t * d₂ = 0) (hne : ¬ (d₁ = 0 ∧ d₂ = 0)) : d₁ * d₂ < 0 := by
  by_cases hd₁ : d₁ = 0
  · subst hd₁
    have : d₂ = 0 := by
      have : t * d₂ = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · exact h'
    exact absurd ⟨rfl, this⟩ hne
  · have key : t * (d₁ * d₂) = -((1 - t) * d₁ ^ 2) := by linear_combination d₁ * h
    have hsq : 0 < d₁ ^ 2 := by positivity
    nlinarith

/-- If `(1 - t) d₁ + t d₂ = 0` with `0 < t < 1`, the values do not have the
same strict sign. -/
theorem mul_nonpos_of_interpolate_eq_zero {d₁ d₂ t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1)
    (h : (1 - t) * d₁ + t * d₂ = 0) : d₁ * d₂ ≤ 0 := by
  have key : t * (d₁ * d₂) = -((1 - t) * d₁ ^ 2) := by linear_combination d₁ * h
  nlinarith [sq_nonneg d₁]

/-- Of two overlapping closed intervals, one contains the other's lower end. -/
theorem min_mem_uIcc_of_inter {a b c d x : ℝ} (h₁ : x ∈ uIcc a b) (h₂ : x ∈ uIcc c d) :
    min c d ∈ uIcc a b ∨ min a b ∈ uIcc c d := by
  rw [uIcc, mem_Icc] at h₁ h₂ ⊢
  rw [uIcc, mem_Icc]
  rcases le_total (min c d) (min a b) with h | h
  · right
    exact ⟨h, h₁.1.trans h₂.2⟩
  · left
    exact ⟨h, h₂.1.trans h₁.2⟩

theorem mem_uIcc_of_lerp {a b t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (1 - t) * a + t * b ∈ uIcc a b := by
  rw [← segment_eq_uIcc]
  exact ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, by simp [smul_eq_mul]⟩

/-! ## Proper intersection -/

/-- Where the lines of two segments cross, read along the first: the point
at parameter `d₁ / (d₁ - d₂)`. -/
noncomputable def crossingPoint (s t : Segment) : Point2D :=
  let d₁ := orient t.p t.q s.p
  let d₂ := orient t.p t.q s.q
  (1 - d₁ / (d₁ - d₂)) • s.p + (d₁ / (d₁ - d₂)) • s.q

/-- `orient t.p t.q` at `s.p` minus at `s.q` is the cross product of the
directions. -/
theorem orient_sub_orient (s t : Segment) :
    orient t.p t.q s.p - orient t.p t.q s.q = cross s.direction t.direction := by
  simp only [orient_def, cross, Segment.direction, x_sub, y_sub]
  ring

theorem cross_direction_comm (s t : Segment) :
    cross t.direction s.direction = -cross s.direction t.direction := cross_comm _ _

/-- A parameter `d₁ / (d₁ - d₂)` with `d₁ d₂ < 0` lies strictly between `0`
and `1`. -/
theorem div_sub_mem_Ioo {d₁ d₂ : ℝ} (h : d₁ * d₂ < 0) : d₁ / (d₁ - d₂) ∈ Ioo (0 : ℝ) 1 := by
  rcases lt_or_gt_of_ne (show d₁ ≠ 0 by rintro rfl; simp at h) with h₁ | h₁
  · have h₂ : 0 < d₂ := by nlinarith
    have hD : d₁ - d₂ < 0 := by linarith
    constructor
    · exact div_pos_of_neg_of_neg h₁ hD
    · rw [div_lt_one_of_neg hD]; linarith
  · have h₂ : d₂ < 0 := by nlinarith
    have hD : 0 < d₁ - d₂ := by linarith
    constructor
    · exact div_pos h₁ hD
    · rw [div_lt_one hD]; linarith

/-- The crossing point read along the second segment is the same point. -/
theorem crossingPoint_comm (s t : Segment) (h : cross s.direction t.direction ≠ 0) :
    crossingPoint s t = crossingPoint t s := by
  have hD : orient t.p t.q s.p - orient t.p t.q s.q ≠ 0 := by rwa [orient_sub_orient]
  have hD' : orient s.p s.q t.p - orient s.p s.q t.q ≠ 0 := by
    rwa [orient_sub_orient, cross_direction_comm, neg_ne_zero]
  apply Point2D.ext
  · simp only [crossingPoint, x_add, x_smul]
    field_simp
    simp only [orient_def]
    ring
  · simp only [crossingPoint, y_add, y_smul]
    field_simp
    simp only [orient_def]
    ring

/-- If `s`'s endpoints straddle `t`'s line, the crossing point lies inside `s`. -/
theorem crossingPoint_mem_relInterior {s t : Segment} (h : Straddles t s) :
    crossingPoint s t ∈ s.relInterior :=
  s.mem_relInterior_iff_exists.mpr ⟨_, div_sub_mem_Ioo h, rfl⟩

/-- The strict test decides proper intersection, with no assumption. -/
theorem properlyIntersect_iff_crossTest (s t : Segment) :
    ProperlyIntersect s t ↔ CrossTest s t := by
  constructor
  · rintro ⟨hpar, x, hxs, hxt⟩
    obtain ⟨a, ha, hax⟩ := s.mem_relInterior_iff_exists.mp hxs
    obtain ⟨b, hb, hbx⟩ := t.mem_relInterior_iff_exists.mp hxt
    have hxt' : orient t.p t.q x = 0 := t.orient_eq_zero_of_mem (t.relInterior_subset_toSet hxt)
    have hxs' : orient s.p s.q x = 0 := s.orient_eq_zero_of_mem (s.relInterior_subset_toSet hxs)
    rw [← hax, orient_lineMap] at hxt'
    rw [← hbx, orient_lineMap] at hxs'
    refine ⟨?_, ?_⟩
    · refine mul_neg_of_interpolate_eq_zero hb.1 hb.2 hxs' ?_
      rintro ⟨h₁, h₂⟩
      apply hpar
      rw [← neg_eq_zero, ← cross_direction_comm, ← orient_sub_orient, h₁, h₂, sub_zero]
    · refine mul_neg_of_interpolate_eq_zero ha.1 ha.2 hxt' ?_
      rintro ⟨h₁, h₂⟩
      apply hpar
      rw [← orient_sub_orient, h₁, h₂, sub_zero]
  · rintro ⟨hst, hts⟩
    have hpar : cross s.direction t.direction ≠ 0 := by
      rw [← orient_sub_orient]
      intro h
      have : orient t.p t.q s.p = orient t.p t.q s.q := by linarith
      unfold Straddles at hts
      rw [this] at hts
      nlinarith [sq_nonneg (orient t.p t.q s.q)]
    refine ⟨hpar, crossingPoint s t, crossingPoint_mem_relInterior hts, ?_⟩
    rw [crossingPoint_comm s t hpar]
    exact crossingPoint_mem_relInterior hst

theorem intersects_of_properlyIntersect {s t : Segment} (h : ProperlyIntersect s t) :
    Intersects s t :=
  let ⟨_, x, hxs, hxt⟩ := h
  ⟨x, s.relInterior_subset_toSet hxs, t.relInterior_subset_toSet hxt⟩

/-! ## General position -/

/-- In general position, the strict test decides intersection: touching is
impossible. -/
theorem intersects_iff_crossTest_of_generalPosition {s t : Segment} (hg : GeneralPosition s t) :
    Intersects s t ↔ CrossTest s t := by
  constructor
  · rintro ⟨x, hxs, hxt⟩
    obtain ⟨a, ha, hax⟩ := s.mem_toSet_iff_exists.mp hxs
    obtain ⟨b, hb, hbx⟩ := t.mem_toSet_iff_exists.mp hxt
    have hxt' := t.orient_eq_zero_of_mem hxt
    have hxs' := s.orient_eq_zero_of_mem hxs
    rw [← hax, orient_lineMap] at hxt'
    rw [← hbx, orient_lineMap] at hxs'
    obtain ⟨g₁, g₂, g₃, g₄⟩ := hg
    have open_of : ∀ {d₁ d₂ t : ℝ}, t ∈ Icc (0 : ℝ) 1 → d₁ ≠ 0 → d₂ ≠ 0 →
        (1 - t) * d₁ + t * d₂ = 0 → t ∈ Ioo (0 : ℝ) 1 := by
      intro d₁ d₂ t ht h₁ h₂ h
      refine ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩
      · rintro rfl; simp at h; exact h₁ h
      · rintro rfl; simp at h; exact h₂ h
    have hb' := open_of hb g₁ g₂ hxs'
    have ha' := open_of ha g₃ g₄ hxt'
    exact ⟨mul_neg_of_interpolate_eq_zero hb'.1 hb'.2 hxs' (fun h => g₁ h.1),
      mul_neg_of_interpolate_eq_zero ha'.1 ha'.2 hxt' (fun h => g₃ h.1)⟩
  · intro h
    exact intersects_of_properlyIntersect ((properlyIntersect_iff_crossTest s t).mpr h)

/-! ## On a segment -/

/-- On a line with direction `u`, a coordinate `f` with `f u ≠ 0` reads the
position: this is what makes `f` usable to test membership. -/
structure Reads (f : Point2D →ₗ[ℝ] ℝ) : Prop where
  /-- If `w` is parallel to `u` and `f u ≠ 0`, `w` is `(f w / f u) • u`. -/
  eq_smul : ∀ {u w : Point2D}, f u ≠ 0 → cross u w = 0 → w = (f w / f u) • u

/-- The first coordinate, as a linear map. -/
noncomputable def xL : Point2D →ₗ[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 2) : Point2D →L[ℝ] ℝ)

/-- The second coordinate, as a linear map. -/
noncomputable def yL : Point2D →ₗ[ℝ] ℝ := (EuclideanSpace.proj (1 : Fin 2) : Point2D →L[ℝ] ℝ)

@[simp] theorem xL_apply (p : Point2D) : xL p = p.x := rfl
@[simp] theorem yL_apply (p : Point2D) : yL p = p.y := rfl

theorem reads_xL : Reads xL := by
  refine ⟨fun {u w} hu h => Point2D.ext ?_ ?_⟩
  · simp only [xL_apply] at hu ⊢
    simp only [x_smul]
    field_simp
  · simp only [xL_apply] at hu ⊢
    simp only [y_smul]
    unfold cross at h
    field_simp
    linarith

theorem reads_yL : Reads yL := by
  refine ⟨fun {u w} hu h => Point2D.ext ?_ ?_⟩
  · simp only [yL_apply] at hu ⊢
    simp only [x_smul]
    unfold cross at h
    field_simp
    linarith
  · simp only [yL_apply] at hu ⊢
    simp only [y_smul]
    field_simp

/-- A scalar `a + τ d` between `a` and `a + d`, `d ≠ 0`, has `τ` in `[0, 1]`. -/
theorem mem_Icc_of_add_mul_mem_uIcc {a d τ : ℝ} (hd : d ≠ 0) (h : a + τ * d ∈ uIcc a (a + d)) :
    τ ∈ Icc (0 : ℝ) 1 := by
  rw [mem_uIcc] at h
  rcases lt_or_gt_of_ne hd with hd | hd
  · rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  · rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · constructor <;> nlinarith
    · constructor <;> nlinarith

/-- With a reading coordinate `f` that separates the endpoints, a collinear
point is on the segment when its `f` lies between the endpoints'. -/
theorem mem_toSet_of_reads {f : Point2D →ₗ[ℝ] ℝ} (hf : Reads f) {s : Segment} {x : Point2D}
    (hne : f s.p ≠ f s.q) (hx : orient s.p s.q x = 0) (hfx : f x ∈ uIcc (f s.p) (f s.q)) :
    x ∈ s.toSet := by
  have hu : f (s.q - s.p) ≠ 0 := by rw [map_sub]; exact sub_ne_zero.mpr hne.symm
  have hw := hf.eq_smul hu hx
  set τ := f (x - s.p) / f (s.q - s.p)
  have hτ : τ ∈ Icc (0 : ℝ) 1 := by
    apply mem_Icc_of_add_mul_mem_uIcc (a := f s.p) hu
    have : f s.p + τ * f (s.q - s.p) = f x := by
      have h' := congrArg f hw
      rw [map_smul, smul_eq_mul, map_sub] at h'
      linarith
    rw [this, map_sub, add_sub_cancel]
    exact hfx
  refine s.mem_toSet_iff_exists.mpr ⟨τ, hτ, ?_⟩
  have : x = s.p + τ • (s.q - s.p) := by rw [← hw]; abel
  rw [this, smul_sub, sub_smul, one_smul]
  abel

/-- A point is on a segment exactly when it is collinear with the endpoints
and each of its coordinates lies between theirs. -/
theorem mem_toSet_iff (s : Segment) (x : Point2D) :
    x ∈ s.toSet ↔ orient s.p s.q x = 0 ∧ x.x ∈ uIcc s.p.x s.q.x ∧ x.y ∈ uIcc s.p.y s.q.y := by
  constructor
  · intro hx
    refine ⟨s.orient_eq_zero_of_mem hx, ?_, ?_⟩ <;>
    · obtain ⟨t, ht, rfl⟩ := s.mem_toSet_iff_exists.mp hx
      simpa using mem_uIcc_of_lerp ht
  · rintro ⟨ho, hx, hy⟩
    by_cases hpx : s.p.x = s.q.x
    · by_cases hpy : s.p.y = s.q.y
      · have hpq : s.p = s.q := Point2D.ext hpx hpy
        rw [hpx, uIcc_self, mem_singleton_iff] at hx
        rw [hpy, uIcc_self, mem_singleton_iff] at hy
        rw [show x = s.q from Point2D.ext hx hy]
        exact s.q_mem_toSet
      · exact mem_toSet_of_reads reads_yL hpy ho hy
    · exact mem_toSet_of_reads reads_xL hpx ho hx

/-! ## Every case -/

/-- If both endpoints of `s` lie on `t`'s line, they and the endpoints of `t`
are all collinear. -/
theorem orient_eq_zero_of_on_line {s t : Segment} (ht : t.p ≠ t.q) (h₁ : orient t.p t.q s.p = 0)
    (h₂ : orient t.p t.q s.q = 0) (z : Point2D) (hz : orient t.p t.q z = 0) :
    orient s.p s.q z = 0 := by
  have hu : t.q - t.p ≠ 0 := sub_ne_zero.mpr ht.symm
  obtain ⟨α, hα⟩ := exists_smul_of_cross_eq_zero hu h₁
  obtain ⟨β, hβ⟩ := exists_smul_of_cross_eq_zero hu h₂
  obtain ⟨γ, hγ⟩ := exists_smul_of_cross_eq_zero hu hz
  have hq : s.q - s.p = (β - α) • (t.q - t.p) := by
    rw [sub_smul, ← hα, ← hβ]; abel
  have hz' : z - s.p = (γ - α) • (t.q - t.p) := by
    rw [sub_smul, ← hα, ← hγ]; abel
  rw [orient, hq, hz', cross_smul_left, cross_smul_right, cross_self, mul_zero, mul_zero]

/-- When `s` lies on `t`'s line and the segments meet, an endpoint of one lies
on the other: overlapping collinear segments. -/
theorem endpoint_mem_of_collinear_of_reads {f : Point2D →ₗ[ℝ] ℝ} (hf : Reads f) {s t : Segment}
    (hft : f t.p ≠ f t.q) (h₁ : orient t.p t.q s.p = 0) (h₂ : orient t.p t.q s.q = 0)
    {x : Point2D} (hxs : x ∈ s.toSet) (hxt : x ∈ t.toSet) :
    t.p ∈ s.toSet ∨ t.q ∈ s.toSet ∨ s.p ∈ t.toSet ∨ s.q ∈ t.toSet := by
  have ht : t.p ≠ t.q := fun h => hft (h ▸ rfl)
  by_cases hs : s.p = s.q
  · obtain ⟨a, -, rfl⟩ := s.mem_toSet_iff_exists.mp hxs
    rw [hs, ← add_smul, sub_add_cancel, one_smul] at hxt
    right; right; left
    rw [hs]; exact hxt
  have hfs : f s.p ≠ f s.q := by
    intro hfeq
    apply hs
    have hu : f (t.q - t.p) ≠ 0 := by rw [map_sub]; exact sub_ne_zero.mpr hft.symm
    have ep := hf.eq_smul hu h₁
    have eq := hf.eq_smul hu h₂
    rw [map_sub, map_sub] at ep eq
    rw [hfeq] at ep
    have : s.p - t.p = s.q - t.p := by rw [ep, eq]
    exact sub_left_injective this
  have hfx : ∀ {r : Segment} {z : Point2D}, z ∈ r.toSet → f z ∈ uIcc (f r.p) (f r.q) := by
    intro r z hz
    obtain ⟨a, ha, rfl⟩ := r.mem_toSet_iff_exists.mp hz
    simpa [map_add, map_smul, smul_eq_mul] using mem_uIcc_of_lerp (a := f r.p) (b := f r.q) ha
  have st₁ := orient_eq_zero_of_on_line ht h₁ h₂ t.p (orient_self₁₃ _ _)
  have st₂ := orient_eq_zero_of_on_line ht h₁ h₂ t.q (orient_self₂₃ _ _)
  rcases min_mem_uIcc_of_inter (hfx hxs) (hfx hxt) with h | h
  · rcases min_choice (f t.p) (f t.q) with e | e <;> rw [e] at h
    · exact Or.inl (mem_toSet_of_reads hf hfs st₁ h)
    · exact Or.inr (Or.inl (mem_toSet_of_reads hf hfs st₂ h))
  · rcases min_choice (f s.p) (f s.q) with e | e <;> rw [e] at h
    · exact Or.inr (Or.inr (Or.inl (mem_toSet_of_reads hf hft h₁ h)))
    · exact Or.inr (Or.inr (Or.inr (mem_toSet_of_reads hf hft h₂ h)))

/-- If the segments meet, either `s`'s endpoints straddle `t`'s line or an
endpoint of one lies on the other. -/
theorem straddles_or_endpoint {s t : Segment} {x : Point2D} (hxs : x ∈ s.toSet)
    (hxt : x ∈ t.toSet) :
    Straddles t s ∨ t.p ∈ s.toSet ∨ t.q ∈ s.toSet ∨ s.p ∈ t.toSet ∨ s.q ∈ t.toSet := by
  obtain ⟨a, ha, hax⟩ := s.mem_toSet_iff_exists.mp hxs
  have hxt' := t.orient_eq_zero_of_mem hxt
  rw [← hax, orient_lineMap] at hxt'
  by_cases hst : Straddles t s
  · exact Or.inl hst
  right
  rcases eq_or_lt_of_le ha.1 with h0 | h0
  · right; right; left
    rw [← h0] at hax; simp at hax; rw [hax]; exact hxt
  rcases eq_or_lt_of_le ha.2 with h1 | h1
  · right; right; right
    rw [h1] at hax; simp at hax; rw [hax]; exact hxt
  -- `s` lies on `t`'s line
  have hle := mul_nonpos_of_interpolate_eq_zero h0 h1 hxt'
  have hz : orient t.p t.q s.p * orient t.p t.q s.q = 0 := le_antisymm hle (not_lt.mp hst)
  have both : orient t.p t.q s.p = 0 ∧ orient t.p t.q s.q = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · refine ⟨h, ?_⟩
      rw [h, mul_zero, zero_add] at hxt'
      exact (mul_eq_zero.mp hxt').resolve_left h0.ne'
    · refine ⟨?_, h⟩
      rw [h, mul_zero, add_zero] at hxt'
      exact (mul_eq_zero.mp hxt').resolve_left (by linarith)
  by_cases htx : t.p.x = t.q.x
  · by_cases hty : t.p.y = t.q.y
    · -- `t` is a single point, which is `x`
      have htt : t.p = t.q := Point2D.ext htx hty
      obtain ⟨b, -, hbx⟩ := t.mem_toSet_iff_exists.mp hxt
      rw [htt, ← add_smul, sub_add_cancel, one_smul] at hbx
      left
      rw [htt, hbx]; exact hxs
    · exact endpoint_mem_of_collinear_of_reads reads_yL hty both.1 both.2 hxs hxt
  · exact endpoint_mem_of_collinear_of_reads reads_xL htx both.1 both.2 hxs hxt

/-- The classical test decides intersection in every case: proper crossing,
endpoint touching and collinear overlap. -/
theorem intersects_iff_intersectTest (s t : Segment) : Intersects s t ↔ IntersectTest s t := by
  constructor
  · rintro ⟨x, hxs, hxt⟩
    rcases straddles_or_endpoint hxs hxt with h₁ | h
    · rcases straddles_or_endpoint hxt hxs with h₂ | h'
      · exact Or.inl ⟨h₂, h₁⟩
      · right; tauto
    · right; exact h
  · rintro (h | h | h | h | h)
    · exact intersects_of_properlyIntersect ((properlyIntersect_iff_crossTest s t).mpr h)
    · exact ⟨t.p, h, t.p_mem_toSet⟩
    · exact ⟨t.q, h, t.q_mem_toSet⟩
    · exact ⟨s.p, s.p_mem_toSet, h⟩
    · exact ⟨s.q, s.q_mem_toSet, h⟩

end ComputationalGeometry
