import LeanComputationalGeometry.Polygon.SignedArea

/-!
# Winding numbers by oriented ray crossings

Cast a ray from `p` horizontally to the right. An edge from `a` to `b`
contributes to the winding number of `p` when it crosses the ray:

- `+1` when it goes upward across the ray's height, `a.y ≤ p.y < b.y`, and
  passes to the right of `p`, which is `orient a b p > 0`;
- `-1` when it goes downward, `b.y ≤ p.y < a.y`, and passes to the right of
  `p`, which is `orient a b p < 0`;
- `0` otherwise (`edgeContribution`).

The half-open intervals count a crossing through a vertex once: of the two
edges meeting at a vertex at the ray's height, the one with the vertex as its
lower end counts it. Degenerate cases are explicit: a horizontal edge never
counts (`edgeContribution_of_horizontal`), and neither does an edge whose line
passes through `p` (`edgeContribution_of_orient_eq_zero`); points on the
boundary are handled by `RawPolygon.OnBoundary`, not by the count.

The winding number of a ring is the sum over its edges (`windingNumber`). It
does not depend on where the ring starts (`windingNumber_rotate`) or where it
is placed (`windingNumber_translate`); traversing the ring the other way
negates it (`windingNumber_reverse`); and it vanishes at points below, above
or to the right of every vertex (`windingNumber_eq_zero_of_below`,
`windingNumber_eq_zero_of_above`, `windingNumber_eq_zero_of_right`).
-/

namespace ComputationalGeometry

open Point2D

open Classical in
/-- The contribution of the edge from `a` to `b` to the winding number of `p`,
counted on the horizontal ray from `p` to the right. -/
noncomputable def edgeContribution (p a b : Point2D) : ℤ :=
  if a.y ≤ p.y ∧ p.y < b.y ∧ 0 < orient a b p then 1
  else if b.y ≤ p.y ∧ p.y < a.y ∧ orient a b p < 0 then -1
  else 0

variable {p a b : Point2D}

/-- An edge crossing the ray's height upward counts `1` if it passes to the
right of `p`. -/
theorem edgeContribution_of_up (ha : a.y ≤ p.y) (hb : p.y < b.y) :
    edgeContribution p a b = if 0 < orient a b p then 1 else 0 := by
  unfold edgeContribution
  by_cases h : 0 < orient a b p
  · simp [ha, hb, h]
  · have : ¬ (b.y ≤ p.y) := not_le.mpr hb
    simp [h, this]

/-- An edge crossing the ray's height downward counts `-1` if it passes to
the right of `p`. -/
theorem edgeContribution_of_down (ha : p.y < a.y) (hb : b.y ≤ p.y) :
    edgeContribution p a b = if orient a b p < 0 then -1 else 0 := by
  unfold edgeContribution
  have : ¬ (a.y ≤ p.y) := not_le.mpr ha
  by_cases h : orient a b p < 0 <;> simp [this, ha, hb, h]

/-- An edge at or below the ray's height does not count. -/
theorem edgeContribution_of_below (ha : a.y ≤ p.y) (hb : b.y ≤ p.y) :
    edgeContribution p a b = 0 := by
  simp [edgeContribution, not_lt.mpr ha, not_lt.mpr hb]

/-- An edge strictly above the ray's height does not count. -/
theorem edgeContribution_of_above (ha : p.y < a.y) (hb : p.y < b.y) :
    edgeContribution p a b = 0 := by
  simp [edgeContribution, not_le.mpr ha, not_le.mpr hb]

/-- A horizontal edge does not count. -/
theorem edgeContribution_of_horizontal (h : a.y = b.y) : edgeContribution p a b = 0 := by
  rcases le_or_gt a.y p.y with ha | ha
  · exact edgeContribution_of_below ha (h ▸ ha)
  · exact edgeContribution_of_above ha (h ▸ ha)

/-- An edge whose line passes through `p` does not count. -/
theorem edgeContribution_of_orient_eq_zero (h : orient a b p = 0) : edgeContribution p a b = 0 := by
  unfold edgeContribution
  simp [h]

/-- An edge with both ends to the left of `p` does not count. -/
theorem edgeContribution_of_right (ha : a.x < p.x) (hb : b.x < p.x) :
    edgeContribution p a b = 0 := by
  have key : orient a b p = (b.x - p.x) * (p.y - a.y) + (p.x - a.x) * (p.y - b.y) := by
    simp only [orient_def]; ring
  unfold edgeContribution
  split_ifs with hup hdown
  · exfalso
    obtain ⟨h₁, h₂, h₃⟩ := hup
    nlinarith [mul_nonneg (sub_pos.mpr hb).le (sub_nonneg.mpr h₁),
      mul_pos (sub_pos.mpr ha) (sub_pos.mpr h₂)]
  · exfalso
    obtain ⟨h₁, h₂, h₃⟩ := hdown
    nlinarith [mul_pos (sub_pos.mpr hb) (sub_pos.mpr h₂), mul_pos (sub_pos.mpr ha) (sub_pos.mpr h₂),
      mul_nonneg (sub_pos.mpr hb).le (sub_nonneg.mpr h₁),
      mul_nonneg (sub_pos.mpr ha).le (sub_nonneg.mpr h₁)]
  · rfl

/-- Reversing an edge negates its contribution. -/
theorem edgeContribution_swap (p a b : Point2D) :
    edgeContribution p b a = -edgeContribution p a b := by
  have hs : orient b a p = -orient a b p := orient_swap₁₂ a b p
  rcases le_or_gt a.y p.y with ha | ha <;> rcases le_or_gt b.y p.y with hb | hb
  · rw [edgeContribution_of_below hb ha, edgeContribution_of_below ha hb, neg_zero]
  · rw [edgeContribution_of_down hb ha, edgeContribution_of_up ha hb]
    simp only [hs, neg_lt_zero]
    split_ifs <;> rfl
  · rw [edgeContribution_of_up hb ha, edgeContribution_of_down ha hb]
    simp only [hs, neg_pos]
    split_ifs <;> rfl
  · rw [edgeContribution_of_above hb ha, edgeContribution_of_above ha hb, neg_zero]

/-- Moving everything by `w` does not change the contribution. -/
theorem edgeContribution_add (p a b w : Point2D) :
    edgeContribution (p + w) (a + w) (b + w) = edgeContribution p a b := by
  simp only [edgeContribution, orient_add_vec, y_add, add_le_add_iff_right, add_lt_add_iff_right]

/-! ## The winding number of a ring -/

namespace RawPolygon

variable (P : RawPolygon)

/-- The winding number of `p`: the sum of the edges' contributions. -/
noncomputable def windingNumber (p : Point2D) : ℤ :=
  ∑ i, edgeContribution p (P.vertex i) (P.vertex (P.next i))

/-- It does not depend on where the ring starts. -/
theorem windingNumber_rotate (p : Point2D) : P.rotate.windingNumber p = P.windingNumber p :=
  Equiv.sum_comp (finRotate P.n) (fun i => edgeContribution p (P.vertex i) (P.vertex (finRotate P.n i)))

/-- Traversing the ring the other way negates it. -/
theorem windingNumber_reverse (p : Point2D) : P.reverse.windingNumber p = -P.windingNumber p := by
  show ∑ i : Fin P.n, edgeContribution p (P.vertex (Fin.rev i))
    (P.vertex (Fin.rev (finRotate P.n i))) = _
  simp only [rev_finRotate]
  have hrev := Equiv.sum_comp Fin.revPerm
    (fun j => edgeContribution p (P.vertex j) (P.vertex ((finRotate P.n).symm j)))
  simp only [Fin.revPerm_apply] at hrev
  rw [hrev, ← Equiv.sum_comp (finRotate P.n)
    (fun j => edgeContribution p (P.vertex j) (P.vertex ((finRotate P.n).symm j)))]
  simp only [Equiv.symm_apply_apply, windingNumber, next]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => edgeContribution_swap _ _ _

/-- Moving the ring and the point together does not change it. -/
theorem windingNumber_translate (p w : Point2D) :
    (P.translate w).windingNumber (p + w) = P.windingNumber p := by
  show ∑ i : Fin P.n, edgeContribution (p + w) (P.vertex i + w) (P.vertex (finRotate P.n i) + w) = _
  simp only [edgeContribution_add]
  rfl

/-- It vanishes below every vertex. -/
theorem windingNumber_eq_zero_of_below {p : Point2D} (h : ∀ i, p.y < (P.vertex i).y) :
    P.windingNumber p = 0 :=
  Finset.sum_eq_zero fun i _ => edgeContribution_of_above (h i) (h _)

/-- It vanishes at or above every vertex. -/
theorem windingNumber_eq_zero_of_above {p : Point2D} (h : ∀ i, (P.vertex i).y ≤ p.y) :
    P.windingNumber p = 0 :=
  Finset.sum_eq_zero fun i _ => edgeContribution_of_below (h i) (h _)

/-- It vanishes to the right of every vertex. -/
theorem windingNumber_eq_zero_of_right {p : Point2D} (h : ∀ i, (P.vertex i).x < p.x) :
    P.windingNumber p = 0 :=
  Finset.sum_eq_zero fun i _ => edgeContribution_of_right (h i) (h _)

end RawPolygon

end ComputationalGeometry
