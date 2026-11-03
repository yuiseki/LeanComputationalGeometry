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

/-- A list of index triangles that triangulates the polygon: every triangle
counterclockwise, and the directed sides cancelling in pairs except for the
polygon's edges. -/
structure IsTriangulation (ts : List (Fin P.n × Fin P.n × Fin P.n)) : Prop where
  isCCW : ∀ t ∈ ts, (P.idxTriangle t).IsCCW
  sides : ∀ u v, P.sideCount ts u v + P.edgeCount v u = P.sideCount ts v u + P.edgeCount u v

variable {P}

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

end RawPolygon

end ComputationalGeometry
