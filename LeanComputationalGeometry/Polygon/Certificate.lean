import LeanComputationalGeometry.Polygon.EarClip

/-!
# Checking a triangulation

An external triangulator (Earcut or any other) hands back triangles as triples
of vertex indices. `IsTriangulation P ts` is a check of such a list `ts`
against a polygon `P`, in two parts:

- `isCCW`: every triangle turns left, `0 < orient`;
- `sides`: the directed sides of the triangles cancel in pairs except for the
  edges of the polygon. For every pair of indices `u`, `v`, the number of
  sides from `u` to `v` minus those from `v` to `u` is the same for the
  triangles as for the polygon's edges.

The second part is a statement about indices only, decidable by `decide`; the
first is a sign test on coordinates.

Neither part mentions the regions, but together they pin them down. Any sum
over directed edges of a function that changes sign with the direction is the
same over the triangles' sides as over the polygon's edges
(`IsTriangulation.sum_sides_eq`), so the winding numbers of the triangles add
up to the polygon's (`IsTriangulation.windingNumber_eq_sum`), and so do the
signed areas (`IsTriangulation.signedArea2_eq_sum`). Off the finitely many
lines through two vertices, a dense open set (`dense_offLines`), a
counterclockwise triangle winds once around the points inside it and never
around the others, so the polygon's winding number counts the triangles
around the point. For a simple polygon it is at most `1`, which gives:

- `IsTriangulation.isCCW`: the polygon is counterclockwise;
- `IsTriangulation.pairwise_disjoint`: the triangles' interiors do not overlap;
- `IsTriangulation.mem_region_iff`: the closed triangles cover the closed
  region exactly.

The last uses that the closed region is the closure of the open region
(`IsSimple.closure_openRegion`), proved with ear clipping.

The check is also complete: ear clipping's triangles, as indices, pass it
(`IsSimple.exists_isTriangulation`, with `n - 2` triangles). Each step moves
the ear to the last vertex, which relabels the vertices
(`IsTriangulation.relabel`), and adds the ear triangle at the last vertex to a
triangulation of the ring without it (`isTriangulation_cons_dropLast`). So a
simple polygon has a list that passes exactly when it is counterclockwise
(`IsSimple.exists_isTriangulation_iff`).
-/

namespace ComputationalGeometry

open Set Point2D

/-! ## Points off finitely many lines -/

/-- The points off the line through two different points are dense. -/
theorem dense_orient_ne_zero {a b : Point2D} (hab : a ≠ b) : Dense {q | orient a b q ≠ 0} := by
  rw [Metric.dense_iff]
  intro x r hr
  by_cases hx : orient a b x ≠ 0
  · exact ⟨x, Metric.mem_ball_self hr, hx⟩
  push Not at hx
  set dx := b.x - a.x
  set dy := b.y - a.y
  have hd : 0 < dx ^ 2 + dy ^ 2 := by
    by_contra hd
    have h1 : dx = 0 := by nlinarith [sq_nonneg dx, sq_nonneg dy]
    have h2 : dy = 0 := by nlinarith [sq_nonneg dx, sq_nonneg dy]
    exact hab (Point2D.ext (by simp only [dx] at h1; linarith) (by simp only [dy] at h2; linarith)).symm
  set t := r / (2 * (|dx| + |dy| + 1))
  have hpos : 0 < 2 * (|dx| + |dy| + 1) := by positivity
  have ht : 0 < t := div_pos hr hpos
  refine ⟨x + t • mk (-dy) dx, ?_, ?_⟩
  · rw [Metric.mem_ball]
    calc dist (x + t • mk (-dy) dx) x ≤ |(x + t • mk (-dy) dx).x - x.x| + |(x + t • mk (-dy) dx).y - x.y| :=
          RawPolygon.dist_le_abs_add_abs _ _
      _ = t * (|dy| + |dx|) := by
          simp only [x_add, y_add, x_smul, y_smul, x_mk, y_mk, add_sub_cancel_left, abs_mul,
            abs_neg, abs_of_pos ht]
          ring
      _ < r := by
          have : t * (2 * (|dx| + |dy| + 1)) = r := div_mul_cancel₀ r hpos.ne'
          nlinarith [abs_nonneg dx, abs_nonneg dy]
  · show orient a b (x + t • mk (-dy) dx) ≠ 0
    rw [orient_def] at hx ⊢
    simp only [x_add, y_add, x_smul, y_smul, x_mk, y_mk]
    have : (b.x - a.x) * (x.y + t * dx - a.y) - (b.y - a.y) * (x.x + t * -dy - a.x) =
        t * (dx ^ 2 + dy ^ 2) := by simp only [dx, dy]; linear_combination hx
    rw [this]
    positivity

namespace RawPolygon

variable (P : RawPolygon)

/-- The points off every line through two different vertices. -/
def offLines : Set Point2D :=
  {q | ∀ u v, P.vertex u ≠ P.vertex v → orient (P.vertex u) (P.vertex v) q ≠ 0}

theorem offLines_eq : P.offLines =
    ⋂ uv : {uv : Fin P.n × Fin P.n // P.vertex uv.1 ≠ P.vertex uv.2},
      {q | orient (P.vertex uv.1.1) (P.vertex uv.1.2) q ≠ 0} := by
  ext q
  simp only [offLines, mem_ofPred_eq, mem_iInter, Subtype.forall, Prod.forall]

theorem isOpen_offLines : IsOpen P.offLines := by
  rw [offLines_eq]
  exact isOpen_iInter_of_finite fun uv =>
    isOpen_ne_fun (continuous_orient _ _) continuous_const

theorem dense_offLines : Dense P.offLines := by
  rw [offLines_eq]
  exact dense_iInter_of_isOpen (fun uv => isOpen_ne_fun (continuous_orient _ _) continuous_const)
    fun uv => dense_orient_ne_zero uv.2

variable {P}

theorem IsSimple.not_onBoundary_of_mem_offLines (hP : P.IsSimple) {q : Point2D}
    (hq : q ∈ P.offLines) : ¬ P.OnBoundary q := by
  rintro ⟨e, he⟩
  have hne : P.vertex e ≠ P.vertex (P.next e) := fun h =>
    next_ne_self hP.three_le e (hP.vertex_injective h).symm
  exact hq _ _ hne ((mem_toSet_iff (P.edge e) q).mp he).1

/-! ## Triangles of indices -/

/-- The triangle with corners the vertices at three indices. -/
def idxTriangle (t : Fin P.n × Fin P.n × Fin P.n) : Triangle :=
  ⟨P.vertex t.1, P.vertex t.2.1, P.vertex t.2.2⟩

open Classical in
/-- Off the lines through two vertices, a counterclockwise triangle of
vertices winds once around the points inside it and never around the others. -/
theorem winding3_idxTriangle_of_mem_offLines {t : Fin P.n × Fin P.n × Fin P.n}
    (ht : (P.idxTriangle t).IsCCW) {q : Point2D} (hq : q ∈ P.offLines) :
    (P.idxTriangle t).winding3 q = if q ∈ interior (P.idxTriangle t).toSet then 1 else 0 := by
  set T := P.idxTriangle t
  split_ifs with hi
  · exact Triangle.winding3_eq_one ht ((Triangle.mem_interior_toSet_iff ht q).mp hi)
  by_cases hT : q ∈ T.toSet
  · exfalso
    have hab : ∀ {x y z : Point2D}, 0 < orient x y z → x ≠ y := by
      rintro x y z h rfl; simp at h
    have hT' : 0 < orient T.a T.b T.c := ht
    have hbc : T.b ≠ T.c := hab (z := T.a) (by
      have : orient T.b T.c T.a = orient T.a T.b T.c := by rw [orient_def, orient_def]; ring
      linarith)
    have hca : T.c ≠ T.a := hab (z := T.b) (by
      have : orient T.c T.a T.b = orient T.a T.b T.c := by rw [orient_def, orient_def]; ring
      linarith)
    rcases (Triangle.mem_frontier_toSet_iff_edges ht q).mp ⟨subset_closure hT, hi⟩ with h | h | h
    · exact hq t.1 t.2.1 (hab hT') ((mem_toSet_iff ⟨T.a, T.b⟩ q).mp h).1
    · exact hq t.2.1 t.2.2 hbc ((mem_toSet_iff ⟨T.b, T.c⟩ q).mp h).1
    · exact hq t.2.2 t.1 hca ((mem_toSet_iff ⟨T.c, T.a⟩ q).mp h).1
  · exact Triangle.winding3_eq_zero_of_not_mem ht hT

/-! ## Counting directed sides -/

variable (P)

/-- How many sides of the triangles go from `u` to `v`. -/
def sideCount (ts : List (Fin P.n × Fin P.n × Fin P.n)) (u v : Fin P.n) : ℕ :=
  (ts.map fun t => (if (t.1, t.2.1) = (u, v) then 1 else 0) +
    (if (t.2.1, t.2.2) = (u, v) then 1 else 0) + (if (t.2.2, t.1) = (u, v) then 1 else 0)).sum

/-- Whether the polygon has an edge from `u` to `v`. -/
def edgeCount (u v : Fin P.n) : ℕ := if P.next u = v then 1 else 0

/-- The polygon's directed edge count is positive exactly on its cyclic
successor pairs. -/
theorem edgeCount_pos_iff (u v : Fin P.n) : 0 < P.edgeCount u v ↔ P.next u = v := by
  by_cases h : P.next u = v <;> simp [edgeCount, h]

/-- A directed pair is counted among the triangles' sides exactly when some
triangle in the list contains that directed side. -/
theorem sideCount_pos_iff (ts : List (Fin P.n × Fin P.n × Fin P.n)) (u v : Fin P.n) :
    0 < P.sideCount ts u v ↔
      ∃ t ∈ ts, (t.1, t.2.1) = (u, v) ∨ (t.2.1, t.2.2) = (u, v) ∨
        (t.2.2, t.1) = (u, v) := by
  unfold sideCount
  rw [List.sum_pos_iff_exists_pos_nat]
  constructor
  · rintro ⟨s, hs, hspos⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    by_cases h₁ : (t.1, t.2.1) = (u, v)
    · exact ⟨t, ht, Or.inl h₁⟩
    by_cases h₂ : (t.2.1, t.2.2) = (u, v)
    · exact ⟨t, ht, Or.inr (Or.inl h₂)⟩
    by_cases h₃ : (t.2.2, t.1) = (u, v)
    · exact ⟨t, ht, Or.inr (Or.inr h₃)⟩
    · simp [h₁, h₂, h₃] at hspos
  · rintro ⟨t, ht, hside⟩
    refine ⟨_, List.mem_map.mpr ⟨t, ht, rfl⟩, ?_⟩
    rcases hside with hside | hside | hside <;> simp [hside]

/-- A list of index triangles that triangulates the polygon: every triangle
counterclockwise, and the directed sides cancelling in pairs except for the
polygon's edges. -/
structure IsTriangulation (ts : List (Fin P.n × Fin P.n × Fin P.n)) : Prop where
  isCCW : ∀ t ∈ ts, (P.idxTriangle t).IsCCW
  sides : ∀ u v, P.sideCount ts u v + P.edgeCount v u = P.sideCount ts v u + P.edgeCount u v

variable {P}

/-- Away from the polygon boundary, each directed side occurs as often in
each direction in a checked triangulation. -/
theorem IsTriangulation.sideCount_eq_of_no_edge
    {ts : List (Fin P.n × Fin P.n × Fin P.n)} (h : P.IsTriangulation ts)
    (u v : Fin P.n) (huv : P.next u ≠ v) (hvu : P.next v ≠ u) :
    P.sideCount ts u v = P.sideCount ts v u := by
  have hs := h.sides u v
  simpa [edgeCount, huv, hvu] using hs

/-- An internal side of a checked triangulation occurs in one direction
exactly when it occurs in the other direction. -/
theorem IsTriangulation.sideCount_pos_iff_reverse_pos_of_no_edge
    {ts : List (Fin P.n × Fin P.n × Fin P.n)} (h : P.IsTriangulation ts)
    (u v : Fin P.n) (huv : P.next u ≠ v) (hvu : P.next v ≠ u) :
    0 < P.sideCount ts u v ↔ 0 < P.sideCount ts v u := by
  rw [h.sideCount_eq_of_no_edge u v huv hvu]

/-- The signed difference of triangle-side counts is exactly the signed
difference of boundary-edge counts. -/
theorem IsTriangulation.sideCount_difference_eq_edgeCount_difference
    {ts : List (Fin P.n × Fin P.n × Fin P.n)} (h : P.IsTriangulation ts)
    (u v : Fin P.n) :
    (P.sideCount ts u v : ℤ) - P.sideCount ts v u =
      (P.edgeCount u v : ℤ) - P.edgeCount v u := by
  have hs := h.sides u v
  have hs' : (P.sideCount ts u v : ℤ) + P.edgeCount v u =
      (P.sideCount ts v u : ℤ) + P.edgeCount u v := by exact_mod_cast hs
  omega

/-- Every boundary edge occurs one more time in its forward direction than
in reverse among the sides of a checked triangulation. -/
theorem IsTriangulation.sideCount_eq_reverse_add_one
    {ts : List (Fin P.n × Fin P.n × Fin P.n)} (h : P.IsTriangulation ts)
    (h3 : 3 ≤ P.n) (u v : Fin P.n) (huv : P.next u = v) :
    P.sideCount ts u v = P.sideCount ts v u + 1 := by
  have hrev : P.next v ≠ u := by
    intro hrev
    have hcycle : P.next (P.next u) ≠ u :=
      P.iterate_next_ne u (k := 2) (by norm_num) h3
    exact hcycle (by rw [huv, hrev])
  have hs := h.sides u v
  simp only [edgeCount, huv, hrev, ↓reduceIte] at hs
  omega

/-- Each forward boundary edge is represented by at least one directed side
of a triangle in a checked triangulation. -/
theorem IsTriangulation.exists_triangle_side_of_edge
    {ts : List (Fin P.n × Fin P.n × Fin P.n)} (h : P.IsTriangulation ts)
    (h3 : 3 ≤ P.n) (u v : Fin P.n) (huv : P.next u = v) :
    ∃ t ∈ ts, (t.1, t.2.1) = (u, v) ∨ (t.2.1, t.2.2) = (u, v) ∨
      (t.2.2, t.1) = (u, v) := by
  have hcount := h.sideCount_eq_reverse_add_one h3 u v huv
  have hpos : 0 < P.sideCount ts u v := by omega
  unfold sideCount at hpos
  rw [List.sum_pos_iff_exists_pos_nat] at hpos
  obtain ⟨s, hs, hspos⟩ := hpos
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  refine ⟨t, ht, ?_⟩
  by_cases h₁ : (t.1, t.2.1) = (u, v)
  · exact Or.inl h₁
  by_cases h₂ : (t.2.1, t.2.2) = (u, v)
  · exact Or.inr (Or.inl h₂)
  by_cases h₃' : (t.2.2, t.1) = (u, v)
  · exact Or.inr (Or.inr h₃')
  · simp [h₁, h₂, h₃'] at hspos

/-- Every internal directed side used by a checked triangulation is matched
by a triangle side in the opposite direction. -/
theorem IsTriangulation.exists_opposite_triangle_side
    {ts : List (Fin P.n × Fin P.n × Fin P.n)} (h : P.IsTriangulation ts)
    (u v : Fin P.n) (huv : P.next u ≠ v) (hvu : P.next v ≠ u)
    (hpos : 0 < P.sideCount ts u v) :
    ∃ t ∈ ts, ((t.1, t.2.1) = (u, v) ∨ (t.2.1, t.2.2) = (u, v) ∨
      (t.2.2, t.1) = (u, v)) ∧
      ∃ t' ∈ ts, (t'.1, t'.2.1) = (v, u) ∨ (t'.2.1, t'.2.2) = (v, u) ∨
        (t'.2.2, t'.1) = (v, u) := by
  have hrevpos := (h.sideCount_pos_iff_reverse_pos_of_no_edge u v huv hvu).mp hpos
  obtain ⟨t, ht, hside⟩ := (P.sideCount_pos_iff ts u v).mp hpos
  obtain ⟨t', ht', hside'⟩ := (P.sideCount_pos_iff ts v u).mp hrevpos
  exact ⟨t, ht, hside, t', ht', hside'⟩

/-- Every vertex of a polygon with at least three vertices occurs in a
triangle of any checked triangulation. -/
theorem IsTriangulation.exists_triangle_at_vertex
    {ts : List (Fin P.n × Fin P.n × Fin P.n)} (h : P.IsTriangulation ts)
    (h3 : 3 ≤ P.n) (u : Fin P.n) :
    ∃ t ∈ ts, t.1 = u ∨ t.2.1 = u ∨ t.2.2 = u := by
  obtain ⟨t, ht, hside⟩ := h.exists_triangle_side_of_edge h3 u (P.next u) rfl
  refine ⟨t, ht, ?_⟩
  rcases hside with hside | hside | hside
  · exact Or.inl (Prod.mk.inj hside).1
  · exact Or.inr (Or.inl (Prod.mk.inj hside).1)
  · exact Or.inr (Or.inr (Prod.mk.inj hside).1)

/-- The three vertices of every triangle in a checked triangulation are
pairwise distinct, since its signed double area is positive. -/
theorem IsTriangulation.idxTriangle_vertices_ne
    {ts : List (Fin P.n × Fin P.n × Fin P.n)} (h : P.IsTriangulation ts)
    (t : Fin P.n × Fin P.n × Fin P.n) (ht : t ∈ ts) :
    (P.idxTriangle t).a ≠ (P.idxTriangle t).b ∧
      (P.idxTriangle t).b ≠ (P.idxTriangle t).c ∧
      (P.idxTriangle t).c ≠ (P.idxTriangle t).a := by
  rcases t with ⟨a, b, c⟩
  change (P.vertex a ≠ P.vertex b) ∧ (P.vertex b ≠ P.vertex c) ∧
    (P.vertex c ≠ P.vertex a)
  have hccw := h.isCCW (a, b, c) ht
  change 0 < orient (P.vertex a) (P.vertex b) (P.vertex c) at hccw
  refine ⟨?_, ?_, ?_⟩
  · intro hab
    rw [hab] at hccw
    simp at hccw
  · intro hbc
    rw [hbc] at hccw
    simp at hccw
  · intro hca
    rw [hca] at hccw
    simp at hccw

/-- A checked triangulation of a polygon with at least three vertices is
nonempty. -/
theorem IsTriangulation.nonempty
    {ts : List (Fin P.n × Fin P.n × Fin P.n)} (h : P.IsTriangulation ts)
    (h3 : 3 ≤ P.n) : ts ≠ [] := by
  intro hnil
  subst ts
  set u : Fin P.n := ⟨0, by omega⟩
  have hs := h.sides u (P.next u)
  have h2 : P.next (P.next u) ≠ u := P.iterate_next_ne u (k := 2) (by norm_num) h3
  simp [sideCount, edgeCount, h2] at hs

open scoped Classical

theorem sum_map_sides {M : Type*} [AddCommMonoid M] (g : Fin P.n → Fin P.n → M) :
    ∀ ts : List (Fin P.n × Fin P.n × Fin P.n),
      (ts.map fun t => g t.1 t.2.1 + g t.2.1 t.2.2 + g t.2.2 t.1).sum =
        ∑ u, ∑ v, P.sideCount ts u v • g u v
  | [] => by simp [sideCount]
  | t :: ts => by
    have h1 : ∀ a b : Fin P.n, ∑ u, ∑ v, (if (a, b) = (u, v) then 1 else 0) • g u v = g a b := by
      intro a b
      simp [Prod.ext_iff, ite_smul, ite_and]
    have hc : ∀ u v, P.sideCount (t :: ts) u v = (if (t.1, t.2.1) = (u, v) then 1 else 0) +
        (if (t.2.1, t.2.2) = (u, v) then 1 else 0) + (if (t.2.2, t.1) = (u, v) then 1 else 0) +
        P.sideCount ts u v := fun u v => by simp [sideCount, List.map_cons, List.sum_cons]
    simp only [List.map_cons, List.sum_cons, hc, add_smul, Finset.sum_add_distrib, h1]
    rw [sum_map_sides g ts]

theorem sum_edges_eq_sum_edgeCount {M : Type*} [AddCommMonoid M] (g : Fin P.n → Fin P.n → M) :
    ∑ i, g i (P.next i) = ∑ u, ∑ v, P.edgeCount u v • g u v := by
  simp [edgeCount, ite_smul]

/-- Across all ordered vertex pairs, each triangle contributes its three
directed sides to the side count. -/
theorem sideCount_sum_eq_three_mul_length (ts : List (Fin P.n × Fin P.n × Fin P.n)) :
    (∑ u, ∑ v, P.sideCount ts u v) = 3 * ts.length := by
  calc
    _ = ts.length * 3 := by simpa using (sum_map_sides (P := P) (g := fun _ _ => (1 : ℕ)) ts).symm
    _ = 3 * ts.length := by omega

/-- Across all ordered vertex pairs, the polygon has exactly one counted
directed edge per vertex. -/
theorem edgeCount_sum_eq_n : (∑ u, ∑ v, P.edgeCount u v) = P.n := by
  simpa using (sum_edges_eq_sum_edgeCount (P := P) (g := fun _ _ => (1 : ℕ))).symm

/-- A sum over directed edges, of a function that changes sign with the
direction, is the same over the triangles' sides as over the polygon's edges. -/
theorem IsTriangulation.sum_sides_eq {ts : List (Fin P.n × Fin P.n × Fin P.n)}
    (h : P.IsTriangulation ts) {M : Type*} [AddCommGroup M] (h2 : ∀ x : M, x + x = 0 → x = 0)
    (g : Fin P.n → Fin P.n → M) (hg : ∀ u v, g v u = -g u v) :
    (ts.map fun t => g t.1 t.2.1 + g t.2.1 t.2.2 + g t.2.2 t.1).sum = ∑ i, g i (P.next i) := by
  rw [sum_map_sides, sum_edges_eq_sum_edgeCount]
  -- Swapping the two indices of an antisymmetric sum changes its sign.
  have hswap : ∀ c : Fin P.n → Fin P.n → ℕ,
      ∑ u, ∑ v, c v u • g u v = -∑ u, ∑ v, c u v • g u v := by
    intro c
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hg v u, smul_neg]
  have key : ∑ u, ∑ v, (P.sideCount ts u v + P.edgeCount v u) • g u v =
      ∑ u, ∑ v, (P.sideCount ts v u + P.edgeCount u v) • g u v := by
    simp only [h.sides]
  simp only [add_smul, Finset.sum_add_distrib] at key
  rw [hswap (P.edgeCount), hswap (fun u v => P.sideCount ts u v)] at key
  apply eq_of_sub_eq_zero
  apply h2
  rw [← sub_eq_zero.mpr key]
  abel

theorem IsTriangulation.windingNumber_eq_sum {ts : List (Fin P.n × Fin P.n × Fin P.n)}
    (h : P.IsTriangulation ts) (p : Point2D) :
    P.windingNumber p = (ts.map fun t => (P.idxTriangle t).winding3 p).sum := by
  have := h.sum_sides_eq (fun x hx => by omega)
    (fun u v => edgeContribution p (P.vertex u) (P.vertex v))
    (fun u v => edgeContribution_swap p _ _)
  rw [windingNumber, ← this]
  rfl

theorem IsTriangulation.signedArea2_eq_sum {ts : List (Fin P.n × Fin P.n × Fin P.n)}
    (h : P.IsTriangulation ts) :
    P.signedArea2 = (ts.map fun t => (P.idxTriangle t).signedArea2).sum := by
  have := h.sum_sides_eq (fun x hx => by linarith) (fun u v => cross (P.vertex u) (P.vertex v))
    (fun u v => cross_comm _ _)
  rw [signedArea2, ← this]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  rw [Triangle.signedArea2_eq_cross_sum]
  rfl

/-- Every triangle in a checked triangulation has positive signed double
area. -/
theorem IsTriangulation.signedArea2_pos {ts : List (Fin P.n × Fin P.n × Fin P.n)}
    (h : P.IsTriangulation ts) (t : Fin P.n × Fin P.n × Fin P.n) (ht : t ∈ ts) :
    0 < (P.idxTriangle t).signedArea2 := h.isCCW t ht

/-- The signed area of a polygon certified by a triangle list is the sum of
the signed areas of those triangles. -/
theorem IsTriangulation.signedArea_eq_sum {ts : List (Fin P.n × Fin P.n × Fin P.n)}
    (h : P.IsTriangulation ts) :
    P.signedArea = (ts.map fun t => (P.idxTriangle t).signedArea).sum := by
  rw [RawPolygon.signedArea, h.signedArea2_eq_sum]
  simp only [Triangle.signedArea]
  have hdiv : ∀ l : List ℝ, (l.map fun x => x / 2).sum = l.sum / 2
      := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring
  simpa only [List.map_map, Function.comp_def] using
    (hdiv (ts.map fun t => (P.idxTriangle t).signedArea2)).symm

/-- Off the lines through two vertices, the winding number counts the
triangles around the point. -/
theorem IsTriangulation.windingNumber_eq_count {ts : List (Fin P.n × Fin P.n × Fin P.n)}
    (h : P.IsTriangulation ts) {q : Point2D} (hq : q ∈ P.offLines) :
    P.windingNumber q =
      (ts.map fun t => if q ∈ interior (P.idxTriangle t).toSet then (1 : ℤ) else 0).sum := by
  rw [h.windingNumber_eq_sum]
  congr 1
  exact List.map_congr_left fun t ht => winding3_idxTriangle_of_mem_offLines (h.isCCW t ht) hq

/-- A triangulated polygon with at least three vertices is counterclockwise:
there is a triangle, and the areas add up. -/
theorem IsTriangulation.polygon_isCCW {ts : List (Fin P.n × Fin P.n × Fin P.n)} (h : P.IsTriangulation ts)
    (h3 : 3 ≤ P.n) : P.IsCCW := by
  have hne : ts ≠ [] := by
    rintro rfl
    set u : Fin P.n := ⟨0, by omega⟩
    have := h.sides u (P.next u)
    have h2 : P.next (P.next u) ≠ u := P.iterate_next_ne u (k := 2) (by norm_num) (by omega)
    simp [sideCount, edgeCount, h2] at this
  show 0 < P.signedArea2
  rw [h.signedArea2_eq_sum]
  refine List.sum_pos _ (fun x hx => ?_) (by simpa using hne)
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact h.isCCW t ht

/-- The sum of the signed double areas in a checked triangulation of a
polygon with at least three vertices is positive. -/
theorem IsTriangulation.sum_signedArea2_pos {ts : List (Fin P.n × Fin P.n × Fin P.n)}
    (h : P.IsTriangulation ts) (h3 : 3 ≤ P.n) :
    0 < (ts.map fun t => (P.idxTriangle t).signedArea2).sum := by
  rw [← h.signedArea2_eq_sum]
  exact h.polygon_isCCW h3

/-- Open sets one of which at most contains each point of a dense set do not
overlap. -/
theorem pairwise_disjoint_of_sum_le_one {ι : Type*} (s : ι → Set Point2D) (hs : ∀ i, IsOpen (s i))
    {G : Set Point2D} (hG : Dense G) :
    ∀ l : List ι, (∀ q ∈ G, (l.map fun i => if q ∈ s i then (1 : ℤ) else 0).sum ≤ 1) →
      l.Pairwise fun i j => Disjoint (s i) (s j)
  | [], _ => List.Pairwise.nil
  | i :: l, h => by
    have hnn : ∀ q, ∀ x ∈ l.map fun j => if q ∈ s j then (1 : ℤ) else 0, 0 ≤ x := by
      intro q x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      split_ifs <;> norm_num
    have hi : ∀ q, 0 ≤ if q ∈ s i then (1 : ℤ) else 0 := fun q => by split_ifs <;> norm_num
    refine List.Pairwise.cons (fun j hj => ?_) (pairwise_disjoint_of_sum_le_one s hs hG l
      fun q hq => ?_)
    · rw [Set.disjoint_iff]
      intro x ⟨hxi, hxj⟩
      obtain ⟨q, ⟨hqi, hqj⟩, hqG⟩ :=
        hG.inter_open_nonempty _ ((hs i).inter (hs j)) ⟨x, hxi, hxj⟩
      have h₁ := h q hqG
      have h₂ := List.single_le_sum (hnn q) _ (List.mem_map_of_mem (f := fun j =>
        if q ∈ s j then (1 : ℤ) else 0) hj)
      simp only [List.map_cons, List.sum_cons, hqi, hqj, ite_true] at h₁ h₂
      linarith
    · have := h q hq
      simp only [List.map_cons, List.sum_cons] at this
      linarith [hi q]

/-- The triangles of a triangulation of a simple polygon do not overlap. -/
theorem IsTriangulation.pairwise_disjoint {ts : List (Fin P.n × Fin P.n × Fin P.n)}
    (h : P.IsTriangulation ts) (hP : P.IsSimple) :
    ts.Pairwise fun t t' =>
      Disjoint (interior (P.idxTriangle t).toSet) (interior (P.idxTriangle t').toSet) :=
  pairwise_disjoint_of_sum_le_one _ (fun _ => isOpen_interior) P.dense_offLines ts fun q hq => by
    rw [← h.windingNumber_eq_count hq]
    exact (abs_le.mp (hP.abs_windingNumber_le_one (hP.not_onBoundary_of_mem_offLines hq))).2

/-- The closed triangles of a triangulation of a simple polygon cover its
closed region exactly. -/
theorem IsTriangulation.mem_region_iff {ts : List (Fin P.n × Fin P.n × Fin P.n)}
    (h : P.IsTriangulation ts) (hP : P.IsSimple) {p : Point2D} :
    p ∈ P.region ↔ ∃ t ∈ ts, p ∈ (P.idxTriangle t).toSet := by
  set U := {q | ∃ t ∈ ts, q ∈ (P.idxTriangle t).toSet}
  have hU : IsClosed U := by
    have : U = ⋃ t ∈ {t | t ∈ ts}, (P.idxTriangle t).toSet := by ext; simp [U]
    rw [this]
    exact ts.finite_toSet.isClosed_biUnion fun t ht => Triangle.isClosed_toSet (h.isCCW t ht)
  have hJ := hP.windsZeroOrOne_of_isCCW (h.polygon_isCCW hP.three_le)
  have hnn : ∀ q, ∀ x ∈ ts.map fun t => if q ∈ interior (P.idxTriangle t).toSet then (1 : ℤ) else 0,
      0 ≤ x := by
    intro q x hx
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    split_ifs <;> norm_num
  constructor
  · intro hp
    have hsub : P.openRegion ∩ P.offLines ⊆ U := by
      rintro q ⟨⟨-, hw⟩, hq⟩
      by_contra hn
      apply hw
      rw [h.windingNumber_eq_count hq]
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      simp only [ite_eq_right_iff]
      exact fun hi => absurd ⟨t, ht, interior_subset hi⟩ hn
    have := (P.dense_offLines.open_subset_closure_inter P.isOpen_openRegion)
    exact hU.closure_subset_iff.mpr hsub
      (closure_mono this (closure_mono (Set.Subset.refl _) (hP.region_subset_closure_openRegion hJ hp))
        |> fun h' => by rwa [closure_closure] at h')
  · rintro ⟨t, ht, hpt⟩
    have hT := h.isCCW t ht
    have hsub : interior (P.idxTriangle t).toSet ∩ P.offLines ⊆ P.region := by
      rintro q ⟨hqi, hq⟩
      refine Or.inr fun hw => ?_
      rw [h.windingNumber_eq_count hq] at hw
      have := List.single_le_sum (hnn q) _ (List.mem_map_of_mem (f := fun t =>
        if q ∈ interior (P.idxTriangle t).toSet then (1 : ℤ) else 0) ht)
      rw [hw] at this
      simp [hqi] at this
    rw [← Triangle.closure_interior hT] at hpt
    exact P.isClosed_region.closure_subset_iff.mpr hsub
      (closure_mono (P.dense_offLines.open_subset_closure_inter isOpen_interior) hpt |>
        fun h' => by rwa [closure_closure] at h')

/-- The region of a simple polygon with a checked triangulation is the set of
points lying in one of its closed index triangles. -/
theorem IsTriangulation.region_eq_setOf {ts : List (Fin P.n × Fin P.n × Fin P.n)}
    (h : P.IsTriangulation ts) (hP : P.IsSimple) :
    P.region = {p | ∃ t ∈ ts, p ∈ (P.idxTriangle t).toSet} := by
  ext p
  exact h.mem_region_iff hP

/-- Each closed triangle in a checked triangulation of a simple polygon lies
inside the polygon's closed region. -/
theorem IsTriangulation.triangle_subset_region {ts : List (Fin P.n × Fin P.n × Fin P.n)}
    (h : P.IsTriangulation ts) (hP : P.IsSimple)
    (t : Fin P.n × Fin P.n × Fin P.n) (ht : t ∈ ts) :
    (P.idxTriangle t).toSet ⊆ P.region := by
  intro p hp
  exact (h.mem_region_iff hP).2 ⟨t, ht, hp⟩

/-- Every vertex of a simple polygon with a checked triangulation belongs to
the closed region. -/
theorem IsTriangulation.vertex_mem_region {ts : List (Fin P.n × Fin P.n × Fin P.n)}
    (h : P.IsTriangulation ts) (hP : P.IsSimple) (u : Fin P.n) :
    P.vertex u ∈ P.region := by
  obtain ⟨t, ht, hcorner⟩ := h.exists_triangle_at_vertex hP.three_le u
  apply (h.mem_region_iff hP).2
  refine ⟨t, ht, ?_⟩
  rcases hcorner with ha | hb | hc
  · rw [← ha]
    exact (P.idxTriangle t).a_mem_toSet
  · rw [← hb]
    exact (P.idxTriangle t).b_mem_toSet
  · rw [← hc]
    exact (P.idxTriangle t).c_mem_toSet

/-- The range of the vertex map of a simple polygon with a checked
triangulation is contained in its closed region. -/
theorem IsTriangulation.range_vertex_subset_region
    {ts : List (Fin P.n × Fin P.n × Fin P.n)}
    (h : P.IsTriangulation ts) (hP : P.IsSimple) : Set.range P.vertex ⊆ P.region := by
  rintro p ⟨u, rfl⟩
  exact h.vertex_mem_region hP u

/-! ## Every simple polygon has a triangulation that passes

Ear clipping's triangles, as vertex indices, pass the check. One step of it
cuts the ear at the last vertex, after moving the ear there; the check
survives both: relabelling the vertices (`IsTriangulation.relabel`), and adding the
ear triangle at the last vertex to a triangulation of the ring without it
(`isTriangulation_cons_dropLast`).
-/

/-- A triangle of indices sent along a map of indices. -/
def mapTri {α β : Type*} (f : α → β) (t : α × α × α) : β × β × β := (f t.1, f t.2.1, f t.2.2)

theorem sideCount_cons (t : Fin P.n × Fin P.n × Fin P.n) (ts : List (Fin P.n × Fin P.n × Fin P.n))
    (u v : Fin P.n) :
    P.sideCount (t :: ts) u v = (if (t.1, t.2.1) = (u, v) then 1 else 0) +
      (if (t.2.1, t.2.2) = (u, v) then 1 else 0) + (if (t.2.2, t.1) = (u, v) then 1 else 0) +
      P.sideCount ts u v := by
  simp [sideCount, List.map_cons, List.sum_cons]

theorem sideCount_map {Q : RawPolygon} (f : Fin Q.n → Fin P.n) (hf : Function.Injective f)
    (ts : List (Fin Q.n × Fin Q.n × Fin Q.n)) (a b : Fin Q.n) :
    P.sideCount (ts.map (mapTri f)) (f a) (f b) = Q.sideCount ts a b := by
  unfold sideCount
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp [mapTri, Prod.ext_iff, hf.eq_iff]

theorem sideCount_map_eq_zero {Q : RawPolygon} (f : Fin Q.n → Fin P.n)
    (ts : List (Fin Q.n × Fin Q.n × Fin Q.n)) {u v : Fin P.n}
    (h : (∀ a, f a ≠ u) ∨ ∀ b, f b ≠ v) : P.sideCount (ts.map (mapTri f)) u v = 0 := by
  unfold sideCount
  rw [List.map_map]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
  rcases h with h | h <;> simp [mapTri, Prod.ext_iff, h]

/-- The check survives relabelling the vertices. -/
theorem IsTriangulation.relabel {Q : RawPolygon} (ρ : Relabel Q P)
    {ts : List (Fin Q.n × Fin Q.n × Fin Q.n)} (h : Q.IsTriangulation ts) :
    P.IsTriangulation (ts.map (mapTri ρ.σ)) where
  isCCW t ht := by
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    have := h.isCCW t' ht'
    simpa [idxTriangle, mapTri, ρ.vertex_eq] using this
  sides u v := by
    obtain ⟨a, rfl⟩ := ρ.σ.surjective u
    obtain ⟨b, rfl⟩ := ρ.σ.surjective v
    have he : ∀ a b, P.edgeCount (ρ.σ a) (ρ.σ b) = Q.edgeCount a b := fun a b => by
      simp only [edgeCount, ← ρ.next_eq, ρ.σ.injective.eq_iff]
    rw [sideCount_map _ ρ.σ.injective, sideCount_map _ ρ.σ.injective, he, he]
    exact h.sides a b

local notation "◇" v:max => RawPolygon.mk _ v

/-- Adding the ear triangle at the last vertex to a triangulation of the ring
without it gives a triangulation. -/
theorem isTriangulation_cons_dropLast {l : ℕ} (v : Fin (l + 1 + 1) → Point2D)
    (hear : ((◇v).earTriangle (Fin.last (l + 1))).IsCCW)
    {ts : List (Fin (l + 1) × Fin (l + 1) × Fin (l + 1))}
    (h : (◇(v ∘ Fin.castSucc)).IsTriangulation ts) :
    (◇v).IsTriangulation
      ((Fin.castSucc (Fin.last l), Fin.last (l + 1), 0) :: ts.map (mapTri Fin.castSucc)) := by
  set R := ◇v
  set Q := ◇(v ∘ Fin.castSucc)
  have hnL : R.next (Fin.last (l + 1)) = 0 := next_last v
  have hpL : R.prev (Fin.last (l + 1)) = Fin.castSucc (Fin.last l) := prev_last v
  have hcL : ∀ a : Fin (l + 1), Fin.castSucc a ≠ (Fin.last (l + 1)) := fun a => Fin.castSucc_ne_last a
  refine ⟨fun t ht => ?_, fun u w => ?_⟩
  · rcases List.mem_cons.mp ht with rfl | ht
    · have : R.idxTriangle (Fin.castSucc (Fin.last l), (Fin.last (l + 1)), 0) = R.earTriangle (Fin.last (l + 1)) := by
        simp only [idxTriangle, earTriangle, prevVertex, nextVertex, hnL, hpL]
      rw [this]; exact hear
    · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
      exact h.isCCW t' ht'
  -- The condition is symmetric in `u` and `w`, and trivial when they agree.
  suffices key : ∀ u w, w ≠ (Fin.last (l + 1)) → R.sideCount
      ((Fin.castSucc (Fin.last l), (Fin.last (l + 1)), 0) :: ts.map (mapTri Fin.castSucc)) u w + R.edgeCount w u =
      R.sideCount ((Fin.castSucc (Fin.last l), (Fin.last (l + 1)), 0) :: ts.map (mapTri Fin.castSucc)) w u +
        R.edgeCount u w by
    by_cases hw : w = (Fin.last (l + 1))
    · by_cases hu : u = (Fin.last (l + 1))
      · rw [hu, hw]
      · exact (key w u hu).symm
    · exact key u w hw
  intro u w hw
  obtain ⟨b, rfl⟩ := Fin.exists_castSucc_eq.mpr hw
  have hQnext : ∀ a : Fin (l + 1), a ≠ Fin.last l →
      R.next (Fin.castSucc a) = Fin.castSucc (Q.next a) := fun a ha =>
    (castSucc_dropLast_next v ha).symm
  have hRlast : R.next (Fin.castSucc (Fin.last l)) = (Fin.last (l + 1)) := by
    rw [← hpL, next_prev]
  have hQlast : Q.next (Fin.last l) = 0 := dropLast_next_last v
  have hinj : Function.Injective (Fin.castSucc : Fin (l + 1) → Fin (l + 1 + 1)) :=
    Fin.castSucc_injective _
  have hcL' : Fin.castSucc (Fin.last l) ≠ (Fin.last (l + 1)) := hcL _
  have h0L : (0 : Fin (l + 1 + 1)) ≠ (Fin.last (l + 1)) := by rw [← Fin.castSucc_zero]; exact hcL _
  have hnext : ∀ x, R.next x = (Fin.last (l + 1)) ↔ x = Fin.castSucc (Fin.last l) := fun x => by
    rw [← hRlast, R.next_injective.eq_iff]
  induction u using Fin.lastCases with
  | last =>
    rw [sideCount_cons, sideCount_cons,
      sideCount_map_eq_zero (P := R) (Q := Q) Fin.castSucc ts (Or.inl hcL),
      sideCount_map_eq_zero (P := R) (Q := Q) Fin.castSucc ts (Or.inr hcL)]
    have e₁ : (0 : Fin (l + 1 + 1)) = Fin.castSucc b ↔ b = 0 := by
      rw [← Fin.castSucc_zero, hinj.eq_iff, eq_comm]
    have e₂ : Fin.castSucc (Fin.last l) = Fin.castSucc b ↔ b = Fin.last l := by
      rw [hinj.eq_iff, eq_comm]
    simp only [edgeCount, hnL, hnext, Prod.mk.injEq, hcL', h0L, (hcL b).symm, false_and, and_false,
      true_and, and_true, e₁, e₂, ↓reduceIte]
    split_ifs <;> omega
  | cast a =>
    rw [sideCount_cons, sideCount_cons, sideCount_map (P := R) (Q := Q) Fin.castSucc hinj ts a b,
      sideCount_map (P := R) (Q := Q) Fin.castSucc hinj ts b a]
    -- The edges of the ring with the last vertex, against those without.
    have hab : ∀ x y : Fin (l + 1), R.edgeCount (Fin.castSucc x) (Fin.castSucc y) +
        (if x = Fin.last l ∧ y = 0 then 1 else 0) = Q.edgeCount x y := by
      intro x y
      by_cases hx : x = Fin.last l
      · subst hx
        simp only [edgeCount, hRlast, hQlast, (hcL y).symm, ↓reduceIte, true_and, zero_add]
        by_cases hy : y = 0
        · simp [hy]
        · simp [hy, Ne.symm hy]
      · simp only [edgeCount, hQnext x hx, hinj.eq_iff, hx, false_and, ↓reduceIte, add_zero]
    have hI : ∀ x y : Fin (l + 1),
        ((0 : Fin (l + 1 + 1)), Fin.castSucc (Fin.last l)) = (Fin.castSucc x, Fin.castSucc y) ↔
          (y = Fin.last l ∧ x = 0) := fun x y => by
      rw [Prod.mk.injEq, ← Fin.castSucc_zero, hinj.eq_iff, hinj.eq_iff, eq_comm (a := (0 : Fin (l + 1))),
        eq_comm (a := Fin.last l), and_comm]
    simp only [hI, Prod.mk.injEq, (hcL _).symm, false_and, and_false, ↓reduceIte, zero_add]
    have h₁ := hab a b
    have h₂ := hab b a
    have h₃ : Q.sideCount ts a b + Q.edgeCount b a = Q.sideCount ts b a + Q.edgeCount a b :=
      h.sides a b
    split_ifs at h₁ h₂ ⊢ <;> omega

/-- Every simple polygon winding `0` or `1` times has a list of index
triangles that passes the check, with `n - 2` triangles: ear clipping's. -/
theorem IsSimple.exists_isTriangulation_aux :
    ∀ (m : ℕ) {P : RawPolygon}, P.n = m → P.IsSimple → P.WindsZeroOrOne →
      ∃ ts, P.IsTriangulation ts ∧ ts.length = P.n - 2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro P hm hP hJ
  rcases hP.three_le.eq_or_lt with h3 | h4
  · obtain ⟨n, v⟩ := P
    simp only at h3
    subst h3
    -- The side condition does not look at the coordinates.
    refine ⟨[(0, 1, 2)], ⟨fun t ht => ?_, (by decide : ∀ u w : Fin 3,
      (RawPolygon.mk 3 fun _ => 0).sideCount [(0, 1, 2)] u w + (RawPolygon.mk 3 fun _ => 0).edgeCount w u =
        (RawPolygon.mk 3 fun _ => 0).sideCount [(0, 1, 2)] w u +
          (RawPolygon.mk 3 fun _ => 0).edgeCount u w)⟩, rfl⟩
    rw [List.mem_singleton] at ht
    subst ht
    have hT := hP.isCCW_earTriangle_of_n_eq_three hJ rfl
    have hp : (finRotate 3).symm 1 = 0 := by decide
    have hn : finRotate 3 1 = 2 := by decide
    have h' : (Triangle.mk (v ((finRotate 3).symm 1)) (v 1) (v (finRotate 3 1))).IsCCW := hT
    rw [hp, hn] at h'
    exact h'
  obtain ⟨i, hi⟩ := hP.exists_ear hJ h4
  obtain ⟨_ | _ | l, v⟩ := P
  · exact absurd h4 (by norm_num)
  · exact absurd h4 (by norm_num)
  simp only at hm
  have hQ : (◇((fun j => v (j + (i + 1))) ∘ Fin.castSucc)).IsSimple := hi.isSimple_removeEar hP h4
  have hQJ : (◇((fun j => v (j + (i + 1))) ∘ Fin.castSucc)).WindsZeroOrOne :=
    hi.windsZeroOrOne_removeEar hP h4 hJ
  obtain ⟨ts, hts, hlen⟩ := ih (l + 1) (by omega) rfl hQ hQJ
  have hear : ((◇fun j => v (j + (i + 1))).earTriangle (Fin.last (l + 1))).IsCCW := by
    rw [earTriangle_shiftLast]; exact hi.isCCW
  refine ⟨_, (isTriangulation_cons_dropLast _ hear hts).relabel (shiftLastRelabel v i), ?_⟩
  simp only [List.length_map, List.length_cons, hlen]
  simp only at h4 hlen ⊢
  omega

theorem IsSimple.exists_isTriangulation (hP : P.IsSimple) (hJ : P.WindsZeroOrOne) :
    ∃ ts, P.IsTriangulation ts ∧ ts.length = P.n - 2 :=
  IsSimple.exists_isTriangulation_aux _ rfl hP hJ

/-- For a simple polygon, some list passes the check exactly when the polygon
is counterclockwise: the check is sound and complete. -/
theorem IsSimple.exists_isTriangulation_iff (hP : P.IsSimple) :
    (∃ ts, P.IsTriangulation ts) ↔ P.IsCCW :=
  ⟨fun ⟨_, h⟩ => h.polygon_isCCW hP.three_le, fun h =>
    let ⟨ts, hts, _⟩ := hP.exists_isTriangulation (hP.windsZeroOrOne_of_isCCW h)
    ⟨ts, hts⟩⟩

end RawPolygon

namespace SimplePolygon

/-- Any simple polygon, traversed counterclockwise, has a triangulation that
passes the check. -/
theorem exists_isTriangulation_orientCCW (P : SimplePolygon) :
    ∃ ts, P.orientCCW.1.IsTriangulation ts ∧ ts.length = P.orientCCW.1.n - 2 :=
  P.orientCCW.2.exists_isTriangulation P.windsZeroOrOne_orientCCW

end SimplePolygon

end ComputationalGeometry
