# Toward Rust with lean-rs

This note records what [lean-rs](https://github.com/conao3/lean-rs) could
compile from LeanComputationalGeometry, and why today that is nothing. There
is no Rust code in this repository, and CI does not run lean-rs.

It was written against lean-rs at commit `90bdd9c` (generator version 3, Lean
`v4.35.0`), from its README and its sources (`LeanRust/Marshal.lean`,
`Main.lean`). lean-rs was not run on this library.

## What lean-rs does, and what it guarantees

lean-rs compiles the IR that Lean's compiler produces for a module
(`Lean.Compiler.IR`) to Rust source that mirrors Lean's C backend
(`lean-rust module generate`, or `lean-rust project generate` for a whole
Lake package; `lean!` embeds Lean source in a Rust file). Theorems are not
compiled; they have no IR. What carries over is this: a generated function
computes what the Lean definition computes, so the theorems proved about that
definition describe the values the Rust function returns. That rests on
lean-rs itself (tested against Lean's C backend, not proved), on Lean's
compiler, and on the Rust caller establishing each theorem's hypotheses.

A definition becomes a public Rust function only if every argument and the
result have a Rust type: `Bool` and `Decidable p`, `Nat`, `Int`, fixed-width
integers, `Float`, `Char`, `String`, `List`, `Array`, `Option`, `Except`,
products, `Fin n` with `n` reducing to a literal, and structures and inductive
types built from these. lean-rs skips, with a reason, a definition that has no
IR (`noncomputable`), takes a proof argument, uses a function type, a type
variable, `Subtype`, a type family or a type that is not an inductive type or
holds one that is not (`ℝ` holds a quotient of Cauchy sequences, `Set` is a
predicate), or takes an argument whose type has proof fields.

## Why nothing qualifies

The library is geometry over the real plane `EuclideanSpace ℝ (Fin 2)`
(`Point2D`), which it shares by `rfl` with LeanGeodesy and LeanGeospatial.
Every definition reaches `ℝ` or a type built on it:

| Definitions | What stops lean-rs |
| --- | --- |
| `Point2D.x`, `Point2D.y`, `cross`, `orient`, `Triangle.signedArea2`, `RawPolygon.signedArea2`, `dot` (`Polygon/Jordan.lean`) | arguments and results in `ℝ`, a quotient of Cauchy sequences, and `Point2D`, which wraps a function into it |
| `Point2D.mk`, `Triangle.signedArea`, `RawPolygon.signedArea`, `crossingPoint`, `xL`, `yL`, `Triangle.toPolygon` | `noncomputable` |
| `Straddles`, `CrossTest`, `IntersectTest`, `Triangle.ContainsTest`, `Triangle.StrictContainsTest`, `IsCCW`, `IsCW`, `ConvexVertex`, `ReflexVertex`, `IsEar`, `IsSimple`, `IsTriangulation` | propositions; their decidability over `ℝ` is classical, so they compile to nothing |
| `edgeContribution`, `windingNumber`, `atOrBelow`, `crossRight`, `crossSign`, `crossX`, `winding3` | `noncomputable` (comparisons of reals decided classically) |
| `earClip`, `someEar`, `orientCCW`, `SimplePolygon.earClip` | `noncomputable`: they choose an ear, or an orientation, by `Classical.choice` |
| `RawPolygon`, `ofList`, `next`, `prev`, `edge`, `translate`, `rotate`, `reverse`, `chain`, `shiftLast`, `dropLast`, `removeEar`, `earTriangle`, `idxTriangle` | `RawPolygon.vertex` is a function `Fin n → Point2D`; `Fin P.n` has a bound that is not a literal |
| `SimplePolygon`, `SimplePolygon.reverse`, `SimplePolygon.removeEar` | `Subtype`, with a proof argument for `removeEar` |
| `sideCount`, `edgeCount` | take a `RawPolygon` and indices in `Fin P.n` |
| `mapTri` | type variables and a function argument (it would need `rust_instances`) |
| `region`, `openRegion`, `OnBoundary`, `toSet`, `offLines`, `leftSector`, `thinLeft` | sets |

None of these is changed to make it exportable. The theorems are about real
geometry: `CrossTest` decides `ProperlyIntersect`
(`properlyIntersect_iff_crossTest`) because the coordinates are real
numbers, and `earClip` is a definition whose
properties are separate theorems, made noncomputable on purpose. Replacing
`ℝ` by `Float` would make the definitions computable and the theorems false
or unprovable, since floating-point arithmetic is not a field. The
`decide` checks in `Examples/Certificate.lean` (the side-count balance of an
index triangulation) are evaluated by Lean's kernel as part of a proof, not
by compiled code.

## Changes made for this

None to the Lean code.

## What a Rust port would need, as future work

These are new definitions and new theorems, not preparation, and are not
started:

- Exact coordinates. A version of `orient` and the tests over `ℤ` or `ℚ`
  (inductive types lean-rs can carry), with theorems relating them to the
  real ones through the casts, would make the orientation and segment tests
  computable without floating point.
- The combinatorial half of the certificate checker. `IsTriangulation.sides`
  depends on the polygon only through its vertex count and `next`; a checker
  on `Nat` indices with a theorem tying it to `sideCount` and `edgeCount`
  could be exported. The `isCCW` half needs the exact coordinates above.
- Ear clipping. An executable ear search would need a decidable ear test on
  exact coordinates and a proof that it agrees with `IsEar`; the current
  `earClip` chooses an ear and is not meant to run.

## Open before starting

- Toolchain. lean-rs is pinned to Lean `v4.35.0`; this library, LeanGeodesy
  and LeanGeospatial are on Lean `v4.34.0` and Mathlib `v4.34.0`, and are
  upgraded together (see `AGENTS.md`).
