/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Degree.FinrankAdjoinLeDegreeEqMaxNegOrd
import Nyll.AlgebraicCurves.Divisors.Degree.DegreeLeFinrankAdjoinEqMaxNegOrd
import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index

/-!
# Divisor degree eq finrank adjoin of eq max neg ord
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    Divisor.degree D = (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) :=
  le_antisymm
    (Divisor.degree_le_finrank_adjoin_of_eq_max_neg_ord x hx D hD)
    (Divisor.finrank_adjoin_le_degree_of_eq_max_neg_ord x hx D hD)
end AlgebraicCurves.Divisors.Proofs.Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
end ProofImplementation
