import LeanComputationalGeometry.Polygon.TwoEars
import LeanComputationalGeometry.Examples.EarRegion

/-!
# Two ears

Meisters' Two Ears Theorem on concrete polygons. Each is simple and
counterclockwise, so `IsSimple.exists_two_nonoverlapping_ears_of_isCCW` gives
two ears with disjoint open triangles; for the square and the comb the two
ears are also exhibited by hand.

- the unit square and the L-shaped hexagon of the earlier examples, where a
  vertex on the diagonal of a convex corner already stops that corner from
  being an ear (`ell_not_isEar_zero`);
- a convex pentagon;
- a hexagon with two consecutive collinear vertices: a square with an extra
  vertex in the middle of two of its sides, where the vertices that go
  straight on are not ears but the theorem needs no general position;
- a comb with three teeth and three reflex vertices between them.
-/

namespace ComputationalGeometry.Examples

open ComputationalGeometry Point2D

noncomputable section

/-- A point off a segment, judged by `mem_toSet_iff`. -/
theorem not_mem_segment_of_coords {a b p : Point2D}
    (h : orient a b p = 0 → p.x ∈ Set.uIcc a.x b.x → p.y ∈ Set.uIcc a.y b.y → False) :
    p ∉ segment ℝ a b := fun hp => by
  obtain ⟨e, x, y⟩ := (mem_toSet_iff ⟨a, b⟩ p).mp hp
  exact h e x y

/-! ## The unit square and the L -/

example : ∃ i j : Fin square.n, i ≠ j ∧ square.IsEar i ∧ square.IsEar j ∧
    Disjoint (interior (square.earTriangle i).toSet) (interior (square.earTriangle j).toSet) :=
  square_isSimple.exists_two_nonoverlapping_ears_of_isCCW square_isCCW (by show 4 ≤ 4; norm_num)

/-- The two ears of the square, by hand: opposite corners, on either side of
the diagonal from `(1, 0)` to `(0, 1)`. -/
example : (0 : Fin 4) ≠ 2 ∧ square.IsEar 0 ∧ square.IsEar 2 ∧
    Disjoint (interior (square.earTriangle 0).toSet) (interior (square.earTriangle 2).toSet) := by
  refine ⟨by decide, square_isEar_zero, square_isEar_two, ?_⟩
  rw [Set.disjoint_left]
  intro p h₁ h₂
  rw [Triangle.mem_interior_toSet_iff square_isEar_zero.isCCW, square_earTriangle_zero] at h₁
  rw [Triangle.mem_interior_toSet_iff square_isEar_two.isCCW, square_earTriangle_two] at h₂
  obtain ⟨-, -, a⟩ := h₁
  obtain ⟨-, -, b⟩ := h₂
  norm_num [orient_def] at a b
  linarith

example : ∃ i j : Fin ell.n, i ≠ j ∧ ell.IsEar i ∧ ell.IsEar j ∧
    Disjoint (interior (ell.earTriangle i).toSet) (interior (ell.earTriangle j).toSet) :=
  ell_isSimple.exists_two_nonoverlapping_ears_of_isCCW ell_isCCW (by show 4 ≤ 6; norm_num)

/-- The recursion-ready form: an ear to cut, chosen without a policy. -/
example : ell.IsEar (SimplePolygon.someEar ⟨ell, ell_isSimple⟩
    (ell_isSimple.windsZeroOrOne_of_isCCW ell_isCCW) (by show 4 ≤ 6; norm_num)) :=
  SimplePolygon.isEar_someEar ⟨ell, ell_isSimple⟩ _ _

/-! ## A convex pentagon -/

abbrev pentagon : RawPolygon := ⟨5, ![mk 0 0, mk 2 0, mk 3 2, mk 1 3, mk (-1) 2]⟩

@[simp] theorem finRotate_five_0 : finRotate 5 0 = 1 := by decide
@[simp] theorem finRotate_five_1 : finRotate 5 1 = 2 := by decide
@[simp] theorem finRotate_five_2 : finRotate 5 2 = 3 := by decide
@[simp] theorem finRotate_five_3 : finRotate 5 3 = 4 := by decide
@[simp] theorem finRotate_five_4 : finRotate 5 4 = 0 := by decide

theorem pentagon_isSimple : pentagon.IsSimple := by
  refine ⟨by show 3 ≤ 5; norm_num, fun i => ?_, fun i => ?_, fun i j hij h₁ h₂ => ?_⟩
  · change Fin 5 at i
    fin_cases i <;>
      simp [RawPolygon.edge, RawPolygon.next, Segment.Nondegenerate, pentagon, ext_iff']
  · change Fin 5 at i
    fin_cases i <;> simp only [RawPolygon.edge, RawPolygon.next, Segment.toSet, pentagon] <;> simp <;>
      exact Triangle.segment_inter_segment_eq (by norm_num [orient_def])
  · change Fin 5 at i j
    change finRotate 5 i ≠ j at h₁
    change finRotate 5 j ≠ i at h₂
    fin_cases i <;> fin_cases j <;> simp at hij h₁ h₂ <;>
      simp only [RawPolygon.edge, RawPolygon.next, Segment.toSet, pentagon] <;> simp <;>
      exact disjoint_segment_of_coords fun x e₁ x₁ y₁ e₂ x₂ y₂ => by
        simp only [Set.mem_uIcc, x_mk, y_mk] at x₁ y₁ x₂ y₂
        norm_num [orient_def] at e₁ e₂
        rcases x₁ with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases y₁ with ⟨_, _⟩ | ⟨_, _⟩ <;>
          rcases x₂ with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases y₂ with ⟨_, _⟩ | ⟨_, _⟩ <;>
          linarith

theorem pentagon_isCCW : pentagon.IsCCW := by
  show 0 < ∑ i : Fin 5, cross (pentagon.vertex i) (pentagon.vertex (finRotate 5 i))
  norm_num [Fin.sum_univ_succ, cross]

example : ∃ i, pentagon.IsEar i :=
  pentagon_isSimple.exists_ear_of_isCCW pentagon_isCCW (by show 4 ≤ 5; norm_num)

example : ∃ i j : Fin pentagon.n, i ≠ j ∧ pentagon.IsEar i ∧ pentagon.IsEar j ∧
    Disjoint (interior (pentagon.earTriangle i).toSet) (interior (pentagon.earTriangle j).toSet) :=
  pentagon_isSimple.exists_two_nonoverlapping_ears_of_isCCW pentagon_isCCW
    (by show 4 ≤ 5; norm_num)

/-! ## Consecutive collinear vertices -/

/-- The square `[0,2] × [0,2]` with an extra vertex in the middle of the bottom
and right sides: two vertices go straight on. -/
abbrev squareMid : RawPolygon :=
  ⟨6, ![mk 0 0, mk 1 0, mk 2 0, mk 2 1, mk 2 2, mk 0 2]⟩

theorem squareMid_isSimple : squareMid.IsSimple := by
  refine ⟨by show 3 ≤ 6; norm_num, fun i => ?_, fun i => ?_, fun i j hij h₁ h₂ => ?_⟩
  · change Fin 6 at i
    fin_cases i <;>
      simp [RawPolygon.edge, RawPolygon.next, Segment.Nondegenerate, squareMid, ext_iff']
  · change Fin 6 at i
    fin_cases i <;> simp only [RawPolygon.edge, RawPolygon.next, Segment.toSet, squareMid] <;> simp <;>
      first
      | (refine Triangle.segment_inter_segment_eq ?_; norm_num [orient_def]; done)
      | (refine Triangle.segment_inter_segment_eq_of_not_mem
            (not_mem_segment_of_coords fun e x y => ?_) (not_mem_segment_of_coords fun e x y => ?_) <;>
          simp only [Set.mem_uIcc, x_mk, y_mk] at x y <;> norm_num [orient_def] at e <;>
          rcases x with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases y with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith)
  · change Fin 6 at i j
    change finRotate 6 i ≠ j at h₁
    change finRotate 6 j ≠ i at h₂
    fin_cases i <;> fin_cases j <;> simp at hij h₁ h₂ <;>
      simp only [RawPolygon.edge, RawPolygon.next, Segment.toSet, squareMid] <;> simp <;>
      exact disjoint_segment_of_coords fun x e₁ x₁ y₁ e₂ x₂ y₂ => by
        simp only [Set.mem_uIcc, x_mk, y_mk] at x₁ y₁ x₂ y₂
        norm_num [orient_def] at e₁ e₂
        rcases x₁ with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases y₁ with ⟨_, _⟩ | ⟨_, _⟩ <;>
          rcases x₂ with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases y₂ with ⟨_, _⟩ | ⟨_, _⟩ <;>
          linarith

theorem squareMid_isCCW : squareMid.IsCCW := by
  show 0 < ∑ i : Fin 6, cross (squareMid.vertex i) (squareMid.vertex (finRotate 6 i))
  norm_num [Fin.sum_univ_succ, cross]

/-- The extra vertices go straight on, so they are not ears. -/
example : ¬ squareMid.IsEar 1 := by
  refine RawPolygon.not_isEar_of_locallyDegenerate ?_
  show orient (squareMid.vertex ((finRotate 6).symm 1)) (squareMid.vertex 1)
    (squareMid.vertex (finRotate 6 1)) = 0
  rw [show (finRotate 6).symm 1 = 0 by rw [Equiv.symm_apply_eq]; decide]
  simp [orient_def]

example : ∃ i j : Fin squareMid.n, i ≠ j ∧ squareMid.IsEar i ∧ squareMid.IsEar j ∧
    Disjoint (interior (squareMid.earTriangle i).toSet)
      (interior (squareMid.earTriangle j).toSet) :=
  squareMid_isSimple.exists_two_nonoverlapping_ears_of_isCCW squareMid_isCCW
    (by show 4 ≤ 6; norm_num)

/-! ## A comb -/

/-- A comb with three teeth: the bottom `[0,6] × {0}`, and a zigzag top
with reflex vertices at `(5,1)`, `(3,1)` and `(1,1)`. -/
abbrev comb : RawPolygon :=
  ⟨9, ![mk 0 0, mk 6 0, mk 6 2, mk 5 1, mk 4 2, mk 3 1, mk 2 2, mk 1 1, mk 0 2]⟩

@[simp] theorem finRotate_nine_0 : finRotate 9 0 = 1 := by decide
@[simp] theorem finRotate_nine_1 : finRotate 9 1 = 2 := by decide
@[simp] theorem finRotate_nine_2 : finRotate 9 2 = 3 := by decide
@[simp] theorem finRotate_nine_3 : finRotate 9 3 = 4 := by decide
@[simp] theorem finRotate_nine_4 : finRotate 9 4 = 5 := by decide
@[simp] theorem finRotate_nine_5 : finRotate 9 5 = 6 := by decide
@[simp] theorem finRotate_nine_6 : finRotate 9 6 = 7 := by decide
@[simp] theorem finRotate_nine_7 : finRotate 9 7 = 8 := by decide
@[simp] theorem finRotate_nine_8 : finRotate 9 8 = 0 := by decide

theorem comb_isSimple : comb.IsSimple := by
  refine ⟨by show 3 ≤ 9; norm_num, fun i => ?_, fun i => ?_, fun i j hij h₁ h₂ => ?_⟩
  · change Fin 9 at i
    fin_cases i <;>
      simp [RawPolygon.edge, RawPolygon.next, Segment.Nondegenerate, comb, ext_iff']
  · change Fin 9 at i
    fin_cases i <;> simp only [RawPolygon.edge, RawPolygon.next, Segment.toSet, comb] <;> simp <;>
      exact Triangle.segment_inter_segment_eq (by norm_num [orient_def])
  · change Fin 9 at i j
    change finRotate 9 i ≠ j at h₁
    change finRotate 9 j ≠ i at h₂
    fin_cases i <;> fin_cases j <;> simp at hij h₁ h₂ <;>
      simp only [RawPolygon.edge, RawPolygon.next, Segment.toSet, comb] <;> simp <;>
      exact disjoint_segment_of_coords fun x e₁ x₁ y₁ e₂ x₂ y₂ => by
        simp only [Set.mem_uIcc, x_mk, y_mk] at x₁ y₁ x₂ y₂
        norm_num [orient_def] at e₁ e₂
        rcases x₁ with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases y₁ with ⟨_, _⟩ | ⟨_, _⟩ <;>
          rcases x₂ with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases y₂ with ⟨_, _⟩ | ⟨_, _⟩ <;>
          linarith

theorem comb_isCCW : comb.IsCCW := by
  show 0 < ∑ i : Fin 9, cross (comb.vertex i) (comb.vertex (finRotate 9 i))
  norm_num [Fin.sum_univ_succ, cross]

example : ∃ i j : Fin comb.n, i ≠ j ∧ comb.IsEar i ∧ comb.IsEar j ∧
    Disjoint (interior (comb.earTriangle i).toSet) (interior (comb.earTriangle j).toSet) :=
  comb_isSimple.exists_two_nonoverlapping_ears_of_isCCW comb_isCCW (by show 4 ≤ 9; norm_num)

theorem comb_earTriangle_two : comb.earTriangle 2 = ⟨mk 6 0, mk 6 2, mk 5 1⟩ := by
  simp [RawPolygon.earTriangle, RawPolygon.prevVertex, RawPolygon.nextVertex, RawPolygon.prev,
    RawPolygon.next, show (finRotate 9).symm 2 = 1 by rw [Equiv.symm_apply_eq]; decide]

theorem comb_earTriangle_six : comb.earTriangle 6 = ⟨mk 3 1, mk 2 2, mk 1 1⟩ := by
  simp [RawPolygon.earTriangle, RawPolygon.prevVertex, RawPolygon.nextVertex, RawPolygon.prev,
    RawPolygon.next, show (finRotate 9).symm 6 = 5 by rw [Equiv.symm_apply_eq]; decide]

/-- The tip of the right tooth is an ear. -/
theorem comb_isEar_two : comb.IsEar 2 := by
  have hT : (comb.earTriangle 2).IsCCW := by
    rw [comb_earTriangle_two]
    norm_num [Triangle.IsCCW, Triangle.signedArea2, orient_def]
  refine ⟨hT, fun j h₁ h₂ h₃ => ?_⟩
  rw [show comb.prev 2 = 1 by show (finRotate 9).symm 2 = 1; rw [Equiv.symm_apply_eq]; decide]
    at h₁
  change j ≠ finRotate 9 2 at h₃
  rw [finRotate_nine_2] at h₃
  rw [Triangle.mem_toSet_iff_containsTest hT, comb_earTriangle_two]
  change Fin 9 at j
  fin_cases j
  all_goals first
    | exact absurd rfl h₁
    | exact absurd rfl h₂
    | exact absurd rfl h₃
    | (intro hc; norm_num [Triangle.ContainsTest, comb, orient_def] at hc)

/-- The tip of the left tooth is an ear. -/
theorem comb_isEar_six : comb.IsEar 6 := by
  have hT : (comb.earTriangle 6).IsCCW := by
    rw [comb_earTriangle_six]
    norm_num [Triangle.IsCCW, Triangle.signedArea2, orient_def]
  refine ⟨hT, fun j h₁ h₂ h₃ => ?_⟩
  rw [show comb.prev 6 = 5 by show (finRotate 9).symm 6 = 5; rw [Equiv.symm_apply_eq]; decide]
    at h₁
  change j ≠ finRotate 9 6 at h₃
  rw [finRotate_nine_6] at h₃
  rw [Triangle.mem_toSet_iff_containsTest hT, comb_earTriangle_six]
  change Fin 9 at j
  fin_cases j
  all_goals first
    | exact absurd rfl h₁
    | exact absurd rfl h₂
    | exact absurd rfl h₃
    | (intro hc; norm_num [Triangle.ContainsTest, comb, orient_def] at hc)

/-- The two ears of the comb, by hand: two tooth tips, `x > 5` and `x < 3`. -/
example : (2 : Fin 9) ≠ 6 ∧ comb.IsEar 2 ∧ comb.IsEar 6 ∧
    Disjoint (interior (comb.earTriangle 2).toSet) (interior (comb.earTriangle 6).toSet) := by
  refine ⟨by decide, comb_isEar_two, comb_isEar_six, ?_⟩
  rw [Set.disjoint_left]
  intro p h₁ h₂
  rw [Triangle.mem_interior_toSet_iff comb_isEar_two.isCCW, comb_earTriangle_two] at h₁
  rw [Triangle.mem_interior_toSet_iff comb_isEar_six.isCCW, comb_earTriangle_six] at h₂
  obtain ⟨a₁, a₂, a₃⟩ := h₁
  obtain ⟨b₁, b₂, b₃⟩ := h₂
  norm_num [orient_def] at a₁ a₂ a₃ b₁ b₂ b₃
  linarith

end

end ComputationalGeometry.Examples
