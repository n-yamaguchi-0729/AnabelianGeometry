# AnabelianGeometry (Lean 4.35.0-rc2)

[![Lean](https://github.com/n-yamaguchi-0729/AnabelianGeometry/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/AnabelianGeometry/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A Lean 4 library proving genus-zero weak reconstruction over number fields,
geometric fundamental-group slimness, and explicit genus-zero calculations.
Weak reconstruction establishes a curve isomorphism; realizing the supplied
group isomorphism and the full Grothendieck correspondence remain further goals.

[Library overview and selected results](https://n-yamaguchi-0729.github.io/NYLL/libraries/anabelian-geometry/).

This library is extracted from [NYLL](https://github.com/n-yamaguchi-0729/NYLL).
<!-- nyll-publication:distribution:begin -->
Only the module-level import closure of `Nyll.AnabelianGeometry.All` is bundled. Dependencies retain their canonical `Nyll` imports.

Supporting modules are included from [AbelianVarieties](Nyll/AbelianVarieties/), [AlgebraicCurves](Nyll/AlgebraicCurves/), [ClassFieldTheory](Nyll/ClassFieldTheory/), [EtaleCohomology](Nyll/EtaleCohomology/), [EtaleFundamentalGroups](Nyll/EtaleFundamentalGroups/), [GaloisCohomology](Nyll/GaloisCohomology/), [JacobianVarieties](Nyll/JacobianVarieties/), [ProCGroups](Nyll/ProCGroups/), [SchemeTheory](Nyll/SchemeTheory/), [ValuedFieldTheory](Nyll/ValuedFieldTheory/), [Yamaguchi26AbfaithfulGalois](Nyll/Yamaguchi26AbfaithfulGalois/). These dependency libraries are included only to the extent required by the imports.
<!-- nyll-publication:distribution:end -->

## Scope

<!-- nyll-publication:anabelian-scope:begin -->
The arithmetic results concern smooth geometrically integral genus-zero curves
over number fields with at least three geometric punctures. The geometric
slimness and fundamental-group calculations below concern algebraically closed
fields of characteristic zero. All use the actual finite étale fiber functors.

The broader target is the Grothendieck correspondence for hyperbolic curves:
curve isomorphisms should correspond to arithmetic fundamental-group
isomorphisms over the absolute Galois group, modulo geometric inner conjugation.
<!-- nyll-publication:anabelian-scope:end -->

## Genus-zero arithmetic reconstruction

<!-- nyll-publication:anabelian-genus-zero:begin -->
Let k be a number field and let U₁ and U₂ be opens in smooth proper
geometrically integral curves of geometric genus zero, each with at least
three geometric boundary points. A continuous isomorphism of their pointed
arithmetic fundamental groups commuting with the maps to G_k implies that
U₁ and U₂ are isomorphic over k: [`exists_schemeIso_of_genusZero_arithmeticFundamentalGroupEquiv`](Nyll/AnabelianGeometry/WeightFiltration/GenusZeroNakamura.lean#L638).

No rational point, split compactification, rational boundary, supplied
finite-cover model, or inertia correspondence is required as input.
The finite models and their descent are constructed in the proof.

For complements of finite sets of at least three k-rational points on
the projective line, [`exists_projectiveTransformation_with_inertia_of_arithmeticFundamentalGroupEquiv`](Nyll/AnabelianGeometry/WeightFiltration/RationalConfigurationNakamura.lean#L554) also constructs a projective
linear transformation carrying one puncture set to the other, together
with the puncture bijection characterized by geometric inertia conjugacy.

These are weak reconstruction results in the direction of
[Nakamura’s genus-zero theorem](https://doi.org/10.1515/crll.1990.411.205):
the conclusion produces a curve isomorphism. It does not identify its
induced fundamental-group map with the supplied isomorphism.
<!-- nyll-publication:anabelian-genus-zero:end -->

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

<!-- nyll-publication:anabelian-reconstruction:begin -->
Realization of a prescribed arithmetic fundamental-group isomorphism by the
reconstructed curve map, uniqueness in that correspondence, and reconstruction
for general hyperbolic curves of positive genus remain unfinished.
The selected arithmetic results are over number fields; the general finitely
generated characteristic-zero base-field theorem is not claimed here.
<!-- nyll-publication:anabelian-reconstruction:end -->

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

## Authorship

All original code in this library is written by OpenAI Codex.

[Naganori Yamaguchi](https://github.com/n-yamaguchi-0729) sets the mathematical
goals and scope, directs development, and maintains the library.

## License and acknowledgements

<!-- nyll-publication:credits:begin -->
Apache License 2.0. See [LICENSE](LICENSE).

Included adaptations from [pi1](https://github.com/chrisflav/pi1) and [Anthropic’s Fermat’s Last Theorem project](https://github.com/anthropics/fermats-last-theorem) retain their source-specific copyrights and authors.
The included-file inventories and preserved upstream notices are in [NOTICE](NOTICE).
<!-- nyll-publication:credits:end -->
