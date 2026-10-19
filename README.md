# AnabelianGeometry (Lean 4.35.0-rc2)

[![Lean](https://github.com/n-yamaguchi-0729/AnabelianGeometry/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/AnabelianGeometry/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

This Lean component of [NYLL](https://github.com/n-yamaguchi-0729/NYLL) studies the recovery of algebraic curves from
their étale fundamental groups, with results on genus-zero reconstruction
over number fields, geometric slimness and explicit fundamental-group calculations.
The [mathematical guide](https://n-yamaguchi-0729.github.io/NYLL/libraries/anabelian-geometry/) presents the reconstruction theorems and geometric applications
with links to their formal proofs.

## Scope

<!-- nyll-publication:anabelian-scope:begin -->
The arithmetic results concern smooth geometrically integral genus-zero curves
over number fields with at least three geometric punctures. The geometric
slimness and fundamental-group calculations below concern algebraically closed
fields of characteristic zero.
<!-- nyll-publication:anabelian-scope:end -->

## Main results

| Result | Mathematical content |
| --- | --- |
| [Grothendieck’s conjecture for genus-zero curves over number fields — weak reconstruction](Nyll/AnabelianGeometry/WeightFiltration/GenusZeroNakamura.lean#L638) | For opens in smooth proper geometrically integral genus-zero curves over a number field, each with at least three geometric punctures, an isomorphism of pointed arithmetic fundamental groups over G_k implies an isomorphism of the curves over k. This does not identify the induced group map with the supplied isomorphism. |
| [Proper curve slimness](Nyll/AnabelianGeometry/GeometricFundamentalGroup/ProperCurveSlim.lean) | Slimness of the étale fundamental group of a smooth proper curve model of genus at least two. |
| [Open curve slimness](Nyll/AnabelianGeometry/GeometricFundamentalGroup/OpenCurveSlim.lean) | Slimness for an open curve with nonempty boundary and `2g + r − 2 > 0`, under the stated normality, local Noetherianity and quasi-compactness hypotheses. |

A profinite group is slim if every open subgroup has trivial centralizer in the ambient group.

## Incomplete results

<!-- nyll-publication:anabelian-reconstruction:begin -->
Realization of a prescribed arithmetic fundamental-group isomorphism by the
reconstructed curve map, uniqueness in that correspondence, and reconstruction
for general hyperbolic curves of positive genus or more general finitely
generated characteristic-zero fields remain unfinished.
<!-- nyll-publication:anabelian-reconstruction:end -->

## Public API

Use [leanprover/lean4:v4.35.0-rc2](lean-toolchain) and the Mathlib revision pinned in
[lake-manifest.json](lake-manifest.json). Add this dependency to your project’s
lakefile.toml:

```toml
[[require]]
name = "Nyll"
git = "https://github.com/n-yamaguchi-0729/AnabelianGeometry.git"
rev = "main"
```

Run `lake update Nyll`, then commit your generated lake-manifest.json to retain
the resolved revisions. Import the library in a Lean file:

```lean
import Nyll.AnabelianGeometry.All
```

The standalone distributions share the package name Nyll. Choose one distribution;
for several libraries together, use [NYLL](https://github.com/n-yamaguchi-0729/NYLL).

To build a checkout of this repository, run from its root:

```sh
lake exe cache get
lake --wfail build
```

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
