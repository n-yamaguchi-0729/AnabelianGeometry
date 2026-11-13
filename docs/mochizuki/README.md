# Mochizuki Hom theorem: manuscript and implementation plan

Start with the [implementation plan](MochizukiThmFormalizationPlan_20261113.md)
for the exact Lean target, checklist, dependencies, and acceptance conditions.
Read the [paper PDF](ReworkingMochizukiThm_20261113_142937_JST.pdf) for its
mathematical exposition; the matching
[LaTeX source](ReworkingMochizukiThm_20261113_142937_JST.tex) is also preserved.

## Scope and status

The paper states a geometrically pro-Σ Hom theorem over p-subtame fields for
p ∈ Σ. The Revision 3 implementation plan specifically targets its
geometrically pro-p case, with the full absolute Galois group as arithmetic
quotient. Do not interpret that plan as an already completed formalization
of the general pro-Σ result.

The supplied plan records 0 of 80 Lean implementation tasks VERIFIED.
Its checklist is the implementation progress record. The paper and plan are
not a kernel-verified proof; the repository's existing implementation status
is described separately in the [main README](../../README.md).

## Original files

These three files were supplied together in the FormalizationGC Library folder
on 13 November 2026. They are preserved byte-for-byte under their original
filenames. The PDF is the supplied 21-page document, not a regenerated build.

| File | SHA-256 |
| --- | --- |
| MochizukiThmFormalizationPlan_20261113.md | 7b1b5aa218da196966826da04604e51470603211408d6f992b4fd3913a6e77d1 |
| ReworkingMochizukiThm_20261113_142937_JST.tex | e56bde91ffe4a360debc1aba80fc09a6616997b22622610a535cfd98300aa837 |
| ReworkingMochizukiThm_20261113_142937_JST.pdf | fd484c485404421f4edbfdb2d591475b669f5131b9b453b0b0abad2e58c5bd99 |
