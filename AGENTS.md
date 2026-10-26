# AGENTS.md

Welcome to the mathematical universe of geospatial geometry and geodesy.

It now lives in three repositories:
[LeanGeodesy](https://github.com/yuiseki/LeanGeodesy) carries the curved
Earth down to a flat map,
[LeanComputationalGeometry](https://github.com/yuiseki/LeanComputationalGeometry)
computes geometry on that map, and
[LeanGeospatial](https://github.com/yuiseki/LeanGeospatial) reasons about the
relations between what lies on it. They stand on one plane, one foundation
and one version of Mathlib. To understand the mathematical structure, read
the other repositories as well: their definitions, their theorems and their
AGENTS.md. Before you change the plane, the toolchain or Mathlib here, check
what that change does there.

Guidance for coding agents (and people) working on LeanComputationalGeometry.

## Scope

| Library | Responsibility |
| --- | --- |
| LeanGeodesy | Earth, ellipsoid, geodesics, projections, CRS, tiles |
| LeanComputationalGeometry | orientation, segments, polygons, winding, triangulation, clipping |
| LeanGeospatial | topology, RCC8, DE-9IM, SFA, GeoSPARQL |

## Rules

- Do not create a new point type or a wrapper around points. The plane is
  Mathlib's `EuclideanSpace ℝ (Fin 2)`; `Point2D` is a reducible abbreviation
  of it, and `ComputationalGeometry.Point2D = Geospatial.Point2D = Geodesy.E2`
  must keep holding by `rfl`. Read coordinates with `Point2D.x` and
  `Point2D.y`.
- Do not push geometry computation into LeanGeospatial. It checks reasoning
  about spatial relations and computes nothing; segment intersection,
  point-in-polygon, triangulation and clipping belong here.
- Do not push planar computational geometry into LeanGeodesy. It brings the
  Earth to the plane; what happens on the plane belongs here.
- Do not make this library depend on its siblings, or change their
  dependencies, until the API here is stable. LeanGeospatial has its own small
  shoelace; leave it alone for now.
- Use the same Lean toolchain and Mathlib revision as the siblings (now Lean
  `v4.34.0`, Mathlib `v4.34.0`), and upgrade all three together. A project
  that imports them resolves a single Mathlib.
- Keep theorems and executable algorithms apart. Decisions are propositions
  (`CrossTest`, `IntersectTest`, `Triangle.ContainsTest`) next to the
  geometric notions they decide (`ProperlyIntersect`, `Intersects`,
  `Triangle.toSet`), with theorems connecting them. Constructions are
  definitions whose properties are separate theorems. An executable
  algorithm gets its own definition and a correctness theorem about it.
- Say which cases a theorem covers. Degenerate cases (equal points, collinear
  points, endpoint contact) go into hypotheses such as `GeneralPosition`, or
  into theorems that cover them; they are not hidden.
- Keep the three levels of polygon data apart: a `RawPolygon` is raw ring
  data, `IsSimple` says it is a simple polygon, and `region` /
  `openRegion` / `OnBoundary` give the regions under the nonzero winding
  rule. Claims about "the region a polygon bounds" are made only for simple
  polygons (`SimplePolygon.toRegion`); do not rely on `RawPolygon.region` for
  self-intersecting rings.
- No `sorry`, no `admit`, no `axiom` of your own. Stay within Lean's standard
  axioms (`propext`, `Classical.choice`, `Quot.sound`).
- Prefer Mathlib's definitions (`segment`, `openSegment`, `convexHull`,
  `Collinear`, `AffineIndependent`, `Matrix.det`) to new ones, and generalise
  beyond the real plane only when the API or the proof clearly improves.

## Build and check

```
lake exe cache get
lake build
```

`lake build` must finish with no errors and no warnings. It builds the
examples and the axiom audit in `LeanComputationalGeometry/Axioms.lean`, which
pins the main theorems to the standard axioms with `#guard_msgs`. When you add
a main theorem, add it to the audit, and add a worked example to
`LeanComputationalGeometry/Examples/`.

CI (`.github/workflows/lean_action_ci.yml`) also rejects any `sorry`, `admit`
or `axiom` in the sources and any import of the examples or the audit from
the library, and its `joint` job runs `scripts/joint_check.sh`: the three
libraries must import together, pin the same toolchain and Mathlib, and share
one plane by `rfl`. It uses the siblings' branch of the same name if there is
one, and their `main` otherwise, so a coordinated change can be tested across
all three before merging.

A full build of Mathlib-dependent Lean uses a lot of memory. On a small
machine, set `LEAN_NUM_THREADS` low.

## Conventions

- Identifiers, docstrings, commit messages and the README are in English.
- `README.md` is the reference: keep its theorem tables, trust boundary and
  roadmap in step with the code.
