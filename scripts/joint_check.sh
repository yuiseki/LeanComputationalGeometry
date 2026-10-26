#!/usr/bin/env bash
# Check that LeanGeodesy, LeanGeospatial and LeanComputationalGeometry can be
# imported together and still share one plane.
#
#   scripts/joint_check.sh PATH/TO/LeanGeodesy PATH/TO/LeanGeospatial \
#     PATH/TO/LeanComputationalGeometry [WORKDIR]
#
# It fails if the three pin different Lean toolchains or Mathlib revisions, if
# the joint project does not build, or if a deliberately false line is not
# rejected (which would mean the check itself is not running).
set -euo pipefail

geodesy=$(cd "$1" && pwd)
geospatial=$(cd "$2" && pwd)
compgeom=$(cd "$3" && pwd)
work=${4:-$(mktemp -d)}
mkdir -p "$work"
work=$(cd "$work" && pwd)

mathlib_rev() {
  python3 -c 'import json,sys; m=json.load(open(sys.argv[1])); print(next(p["rev"] for p in m["packages"] if p["name"]=="mathlib"))' "$1/lake-manifest.json"
}

toolchain=$(cat "$compgeom/lean-toolchain")
rev=$(mathlib_rev "$compgeom")
for lib in "$geodesy" "$geospatial"; do
  if [ "$toolchain" != "$(cat "$lib/lean-toolchain")" ]; then
    echo "lean-toolchain differs: $compgeom has $toolchain, $lib has $(cat "$lib/lean-toolchain")" >&2
    exit 1
  fi
  if [ "$rev" != "$(mathlib_rev "$lib")" ]; then
    echo "Mathlib revision differs: $compgeom has $rev, $lib has $(mathlib_rev "$lib")" >&2
    exit 1
  fi
done
echo "All three pin $toolchain and Mathlib $rev"

cd "$work"
echo "$toolchain" > lean-toolchain
cat > lakefile.toml <<TOML
name = "joint"
defaultTargets = ["Joint"]

[[lean_lib]]
name = "Joint"

[[require]]
name = "lean-geodesy"
path = "$geodesy"

[[require]]
name = "lean-geospatial"
path = "$geospatial"

[[require]]
name = "lean-computational-geometry"
path = "$compgeom"
TOML

cat > Joint.lean <<'LEAN'
import LeanGeodesy
import LeanGeospatial
import LeanComputationalGeometry

/-! The three libraries' planes are one type, Mathlib's Euclidean plane. -/

example : ComputationalGeometry.Point2D = Geospatial.Point2D := rfl
example : ComputationalGeometry.Point2D = Geodesy.E2 := rfl
example : Geospatial.Point2D = Geodesy.E2 := rfl

/-- The coordinates read the same. -/
example (p : ComputationalGeometry.Point2D) :
    ComputationalGeometry.Point2D.x p = Geospatial.Point2D.x p := rfl

/-- Points that LeanGeodesy's Mercator projection draws feed this library's
orientation test and its theorems directly. -/
example (R φ₁ l₁ φ₂ l₂ φ₃ l₃ : ℝ) :
    ComputationalGeometry.orient (Geodesy.Projection.mercator R φ₂ l₂)
        (Geodesy.Projection.mercator R φ₁ l₁) (Geodesy.Projection.mercator R φ₃ l₃) =
      -ComputationalGeometry.orient (Geodesy.Projection.mercator R φ₁ l₁)
        (Geodesy.Projection.mercator R φ₂ l₂) (Geodesy.Projection.mercator R φ₃ l₃) :=
  ComputationalGeometry.orient_swap₁₂ _ _ _

/-- A segment of this library is a LeanGeospatial region. -/
example (s : ComputationalGeometry.Segment) : Geospatial.Region := s.toSet

/-- LeanGeospatial's relations apply to this library's triangles. -/
example (T : ComputationalGeometry.Triangle) (A : Geospatial.Region) : Prop :=
  Geospatial.Within T.toSet A
LEAN

cat > False.lean <<'LEAN'
import LeanGeodesy
import LeanGeospatial
import LeanComputationalGeometry

example : (1 : ℕ) = 2 := rfl
LEAN

lake update
lake exe cache get
lake build

if lake env lean False.lean > /dev/null 2>&1; then
  echo "A false statement was accepted: the joint check is not running" >&2
  exit 1
fi
echo "LeanGeodesy, LeanGeospatial and LeanComputationalGeometry share one plane"
