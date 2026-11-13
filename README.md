# AnabelianGeometry (Lean 4.35.0)

[![Lean](https://github.com/n-yamaguchi-0729/AnabelianGeometry/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/AnabelianGeometry/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

This Lean component of [NYLL](https://github.com/n-yamaguchi-0729/NYLL) aims to
formalize the **p-subtame Hom theorem** in the supplied reworking of Mochizuki's
Hom theorem. The source manuscript and the detailed implementation plan are
collected in [docs/mochizuki](docs/mochizuki/README.md).

## Formalization target and source documents

- [Implementation plan (Revision 3, 13 November 2026)](docs/mochizuki/MochizukiThmFormalizationPlan_20261113.md): the task checklist, proof obligations, and implementation order.
- [Paper (PDF)](docs/mochizuki/ReworkingMochizukiThm_20261113_142937_JST.pdf) and [LaTeX source](docs/mochizuki/ReworkingMochizukiThm_20261113_142937_JST.tex): *A Reworking of Mochizuki's Hom Theorem over p-Subtame Fields*.

The manuscript states the geometrically pro-Σ Hom theorem for every set of
primes Σ containing p. For a p-subtame field K, it identifies dominant
K-morphisms from a normal geometrically integral finite-type K-scheme X to a
hyperbolic K-curve Y with continuous open homomorphisms of their geometrically
pro-Σ arithmetic fundamental groups over G_K, modulo geometric inner
automorphisms of the target. The source X need not be separated.

Here p-subtame means that K embeds into the maximal algebraic tamely ramified
extension of a Henselian discretely valued field of mixed characteristic (0,p).
The residue field of that host is arbitrary; K itself need not be complete,
discretely valued, or finitely generated.

**The current implementation plan targets the geometrically pro-p case**
(Σ = {p}), retaining the full arithmetic quotient G_K. It does not yet specify
a Lean implementation of the entire pro-Σ extension. The plan calls for actual
morphisms and fundamental-group maps, realization of each prescribed open
homomorphism, and uniqueness, not only a weak Isom reconstruction statement.
Stacks is the canonical foundation on overlaps with NYLL.

**Status:** the supplied plan records **0 of 80 implementation tasks VERIFIED**.
These documents are a mathematical manuscript and a formalization plan, not
evidence that the target Hom theorem has already been checked in Lean. Adding
them does not change the proved scope of the existing implementation below.

## Existing implementation

The existing code studies the recovery of algebraic curves from their étale
fundamental groups, with results on genus-zero reconstruction over finitely
generated fields of characteristic zero, geometric slimness, and explicit
fundamental-group calculations. The
[mathematical guide](https://n-yamaguchi-0729.github.io/NYLL/libraries/anabelian-geometry/)
presents these existing results with links to their formal proofs.

### Existing scope

<!-- nyll-publication:anabelian-scope:begin -->
The arithmetic results concern smooth geometrically integral genus-zero curves
over fields finitely generated over the rationals with at least three geometric punctures. The geometric
slimness and fundamental-group calculations below concern algebraically closed
fields of characteristic zero.
<!-- nyll-publication:anabelian-scope:end -->

### Existing main results

| Result | Mathematical content |
| --- | --- |
| [Grothendieck’s conjecture for genus-zero curves over finitely generated fields — weak reconstruction](Nyll/AnabelianGeometry/WeightFiltration/GenusZeroNakamura.lean#L647) | For opens in smooth proper geometrically integral genus-zero curves over a field finitely generated over the rationals, each with at least three geometric punctures, an isomorphism of pointed arithmetic fundamental groups over G_k implies an isomorphism of the curves over k. This does not identify the induced group map with the supplied isomorphism. |
| [Proper curve slimness](Nyll/AnabelianGeometry/GeometricFundamentalGroup/ProperCurveSlim.lean) | Slimness of the étale fundamental group of a smooth proper curve model of genus at least two. |
| [Open curve slimness](Nyll/AnabelianGeometry/GeometricFundamentalGroup/OpenCurveSlim.lean) | Slimness for an open curve with nonempty boundary and `2g + r − 2 > 0`, under the stated normality, local Noetherianity and quasi-compactness hypotheses. |

A profinite group is slim if every open subgroup has trivial centralizer in the ambient group.

### Incomplete results

<!-- nyll-publication:anabelian-reconstruction:begin -->
Realization of a prescribed arithmetic fundamental-group isomorphism by the
reconstructed curve map, uniqueness in that correspondence, and reconstruction
for general hyperbolic curves of positive genus or more general finitely
generated characteristic-zero fields remain unfinished.
<!-- nyll-publication:anabelian-reconstruction:end -->

## Public API

Use [leanprover/lean4:v4.35.0](lean-toolchain) and the Mathlib revision pinned in
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
