# AnabelianGeometry (Lean 4.35.0-rc2)

[![Lean](https://github.com/n-yamaguchi-0729/AnabelianGeometry/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/AnabelianGeometry/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A Lean 4 library **under development**, aiming to formalize the Grothendieck
conjecture for hyperbolic curves. It currently develops geometric étale
fundamental groups, their slimness, and explicit genus-zero calculations.

This library is extracted from [NYLL](https://github.com/n-yamaguchi-0729/NYLL).
Bundled dependencies use the same `Nyll` imports as the complete library.

## Scope

The intended Grothendieck theorem identifies isomorphisms of hyperbolic curves
over a finitely generated field of characteristic zero with continuous
isomorphisms of their arithmetic fundamental groups over the absolute Galois
group, modulo conjugation by the target's geometric fundamental group.

The following fundamental-group results are over algebraically closed fields
of characteristic zero. They use the actual geometric fiber functor on finite
étale covers.

## Main results

| Result | Mathematical content |
| --- | --- |
| [Proper curve slimness](Nyll/AnabelianGeometry/GeometricFundamentalGroup/ProperCurveSlim.lean) | Slimness of the étale fundamental group of a smooth proper curve model of genus at least two. |
| [Open curve slimness](Nyll/AnabelianGeometry/GeometricFundamentalGroup/OpenCurveSlim.lean) | Slimness for an open curve with nonempty boundary and `2g + r − 2 > 0`, under the stated normality, local Noetherianity and quasi-compactness hypotheses. |
| [Genus-zero fundamental group](Nyll/AnabelianGeometry/GeometricFundamentalGroup/GenusZeroFundamentalGroup.lean) | Triviality of the fundamental group of a proper genus-zero curve model. |
| [Affine line and one puncture](Nyll/AnabelianGeometry/GeometricFundamentalGroup/AffineLineFundamentalGroup.lean) | Triviality of the fundamental group of the affine line. The [one-puncture theorem](Nyll/AnabelianGeometry/GeometricFundamentalGroup/OnePunctureGenusZero.lean) treats the complement of a point on a proper genus-zero curve. |
| [Two-puncture comparison](Nyll/AnabelianGeometry/GeometricFundamentalGroup/TwoPuncturesFundamentalGroup.lean) | The fundamental group of a genus-zero curve with two punctures is topologically isomorphic to the profinite integers. |

Further proved results include projective-line cross-ratio and multiplicative
rigidity, Kummer power-class separation over number fields, separation and
normalizer criteria for cuspidal inertia, and residue-rank and generic-point
comparisons for the weight filtration. Their precise hypotheses are in
[Projective line](Nyll/AnabelianGeometry/ProjectiveLine/All.lean),
[Kummer theory](Nyll/AnabelianGeometry/KummerTheory/All.lean),
[Cuspidal inertia](Nyll/AnabelianGeometry/CuspidalInertia/All.lean), and
[Weight filtration](Nyll/AnabelianGeometry/WeightFiltration/All.lean).

A profinite group is *slim* if every open subgroup has trivial centralizer in
the ambient group. The proofs realize open subgroups by finite étale covers
and use geometric cohomology and ramification calculations.

## Incomplete results

The Grothendieck conjecture itself is not yet proved in this library.
The arithmetic reconstruction needed for this correspondence remains open
in the formalization.

## Public API

```lean
import Nyll.AnabelianGeometry.All
```

The main slimness results can be imported independently:

```lean
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.ProperCurveSlim
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.OpenCurveSlim
```

## Build

The toolchain and dependencies are pinned in [`lean-toolchain`](lean-toolchain)
and [`lakefile.toml`](lakefile.toml).

```console
lake exe cache get
lake --wfail build
```

[CI](.github/workflows/lean.yml) checks the complete import closure and builds
all libraries in dependency order, with warnings treated as errors.

## Authorship and AI-written code

All original code in this library is written by OpenAI Codex.
[Naganori Yamaguchi](https://github.com/n-yamaguchi-0729) sets the mathematical
goals and scope, directs development, and maintains the library.

## License and acknowledgements

Apache License 2.0. See [LICENSE](LICENSE).
Supporting code includes adaptations from [pi1](https://github.com/chrisflav/pi1)
and [Anthropic FLT](https://github.com/anthropics/fermats-last-theorem); see [NOTICE](NOTICE).
