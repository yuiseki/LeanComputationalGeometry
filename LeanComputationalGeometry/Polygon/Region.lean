import LeanComputationalGeometry.Polygon.Winding

/-!
# The region a polygon bounds

Three sets are attached to a ring, under the nonzero winding rule:

| Name | Points | Meaning |
| --- | --- | --- |
| `OnBoundary P p` | on some edge segment | the boundary |
| `P.region` | `OnBoundary P p ∨ P.windingNumber p ≠ 0` | the closed region |
| `P.openRegion` | `¬ OnBoundary P p ∧ P.windingNumber p ≠ 0` | the open region |

The winding number says nothing reliable on the boundary (an edge through
`p` is not counted), so the boundary is added or removed explicitly.

These are defined for raw rings, but they mean the region a polygon bounds
only for simple polygons: `SimplePolygon.toRegion` and
`SimplePolygon.toOpenRegion` are the sets this library takes a simple
polygon to stand for. For a self-intersecting ring the sets are still
defined, but no claim is made about them. That `toRegion` is the closure of
`toOpenRegion` and `toOpenRegion` the interior of `toRegion` is the Jordan
curve theorem for polygons, which is not proved here; for triangles it is
(`Triangle.mem_toRegion_iff`, `Triangle.mem_toOpenRegion_iff`).

None of the three depends on where the ring starts or which way it runs
(`region_rotate`, `region_reverse`, and the same for the others).
-/

namespace ComputationalGeometry

open Set

namespace RawPolygon

variable (P : RawPolygon)

/-- `p` is on the ring: on some edge segment. -/
def OnBoundary (p : Point2D) : Prop := ∃ i, p ∈ (P.edge i).toSet

/-- The closed region under the nonzero winding rule: the boundary together
with the points of nonzero winding number. -/
def region : Set Point2D := {p | P.OnBoundary p ∨ P.windingNumber p ≠ 0}

/-- The open region under the nonzero winding rule: points off the boundary
with nonzero winding number. -/
def openRegion : Set Point2D := {p | ¬ P.OnBoundary p ∧ P.windingNumber p ≠ 0}

/-- Every vertex is on the boundary. -/
theorem onBoundary_vertex (i : Fin P.n) : P.OnBoundary (P.vertex i) := ⟨i, (P.edge i).p_mem_toSet⟩

/-- Every point inside an edge is on the boundary. -/
theorem onBoundary_of_mem_relInterior {i : Fin P.n} {p : Point2D}
    (h : p ∈ (P.edge i).relInterior) : P.OnBoundary p :=
  ⟨i, (P.edge i).relInterior_subset_toSet h⟩

theorem openRegion_subset_region : P.openRegion ⊆ P.region := fun _ h => Or.inr h.2

theorem onBoundary_subset_region : {p | P.OnBoundary p} ⊆ P.region := fun _ h => Or.inl h

theorem mem_region_iff {p : Point2D} :
    p ∈ P.region ↔ P.OnBoundary p ∨ p ∈ P.openRegion := by
  simp only [region, openRegion, mem_ofPred_eq]
  tauto

theorem onBoundary_rotate (p : Point2D) : P.rotate.OnBoundary p ↔ P.OnBoundary p := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨finRotate P.n i, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨(finRotate P.n).symm i, ?_⟩
    change p ∈ segment ℝ (P.vertex (finRotate P.n ((finRotate P.n).symm i)))
      (P.vertex (finRotate P.n (finRotate P.n ((finRotate P.n).symm i))))
    rw [Equiv.apply_symm_apply]
    exact hi

theorem onBoundary_reverse (p : Point2D) : P.reverse.OnBoundary p ↔ P.OnBoundary p := by
  constructor
  · rintro ⟨i, hi⟩
    have e := P.reverse_edge i
    rw [e, Segment.toSet_swap] at hi
    exact ⟨_, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨Fin.rev (P.next i), ?_⟩
    have e := congrArg Segment.toSet (P.reverse_edge (Fin.rev (P.next i)))
    rw [Segment.toSet_swap, Fin.rev_rev, prev_next] at e
    exact e.symm ▸ hi

theorem region_rotate : P.rotate.region = P.region := by
  ext p
  simp only [region, mem_ofPred_eq, onBoundary_rotate, windingNumber_rotate]

theorem region_reverse : P.reverse.region = P.region := by
  ext p
  simp only [region, mem_ofPred_eq, onBoundary_reverse, windingNumber_reverse, ne_eq, neg_eq_zero]

theorem openRegion_rotate : P.rotate.openRegion = P.openRegion := by
  ext p
  simp only [openRegion, mem_ofPred_eq, onBoundary_rotate, windingNumber_rotate]

theorem openRegion_reverse : P.reverse.openRegion = P.openRegion := by
  ext p
  simp only [openRegion, mem_ofPred_eq, onBoundary_reverse, windingNumber_reverse, ne_eq,
    neg_eq_zero]

/-- Far below, above or to the right of every vertex, a point is not in the
region. -/
theorem not_mem_region_of_below {p : Point2D} (h : ∀ i, p.y < (P.vertex i).y) :
    p ∉ P.region := by
  rintro (⟨i, hi⟩ | hw)
  · obtain ⟨t, ht, rfl⟩ := (P.edge i).mem_toSet_iff_exists.mp hi
    have h₁ := h i
    have h₂ := h (P.next i)
    simp only [edge, Point2D.y_add, Point2D.y_smul] at h₁ h₂
    nlinarith [mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
      (sq_nonneg ((P.vertex (P.next i)).y - (P.vertex i).y))]
  · exact hw (P.windingNumber_eq_zero_of_below h)

theorem not_mem_region_of_right {p : Point2D} (h : ∀ i, (P.vertex i).x < p.x) :
    p ∉ P.region := by
  rintro (⟨i, hi⟩ | hw)
  · obtain ⟨t, ht, rfl⟩ := (P.edge i).mem_toSet_iff_exists.mp hi
    have h₁ := h i
    have h₂ := h (P.next i)
    simp only [edge, Point2D.x_add, Point2D.x_smul] at h₁ h₂
    nlinarith [mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
      (sq_nonneg ((P.vertex (P.next i)).x - (P.vertex i).x))]
  · exact hw (P.windingNumber_eq_zero_of_right h)

end RawPolygon

namespace SimplePolygon

variable (P : SimplePolygon)

/-- The closed region a simple polygon stands for. -/
def toRegion : Set Point2D := P.1.region

/-- The open region a simple polygon stands for. -/
def toOpenRegion : Set Point2D := P.1.openRegion

/-- The boundary of a simple polygon. -/
def boundary : Set Point2D := {p | P.1.OnBoundary p}

theorem toOpenRegion_subset_toRegion : P.toOpenRegion ⊆ P.toRegion := P.1.openRegion_subset_region

theorem boundary_subset_toRegion : P.boundary ⊆ P.toRegion := P.1.onBoundary_subset_region

/-- In a simple polygon, a point on one edge lies on no edge that is not
adjacent to it. -/
theorem not_mem_edge_of_nonadjacent {i j : Fin P.1.n} (hij : i ≠ j) (h₁ : P.1.next i ≠ j)
    (h₂ : P.1.next j ≠ i) {p : Point2D} (hp : p ∈ (P.1.edge i).toSet) : p ∉ (P.1.edge j).toSet :=
  fun hq => (P.2.nonadjacent_disjoint i j hij h₁ h₂).ne_of_mem hp hq rfl

end SimplePolygon

end ComputationalGeometry
