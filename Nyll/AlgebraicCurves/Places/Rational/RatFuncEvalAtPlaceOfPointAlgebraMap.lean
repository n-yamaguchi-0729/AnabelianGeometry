/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_evalAt_placeOfPoint_algebraMap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Nyll.AlgebraicCurves.Places.Rational.FiniteOrder
import Nyll.AlgebraicCurves.Places.Evaluation.EvalAtCongr
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation

/-!
# Polynomial evaluation at a rational point
-/

open Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem AlgebraicCurve.RationalFunctionField.evalAt_placeOfPoint_algebraMap {K : Type*}
  [Field K] (a : K) (q : Polynomial K) : (placeOfPoint K a).evalAt (algebraMap (Polynomial K)
  (RatFunc K) q) = q.eval a := by
  have hmem : algebraMap K[X] (RatFunc K) q ∈ (placeOfPoint K a).toValuationSubring :=
    algebraMap_mem_ofHeightOneSpectrum K _ q
  have hmem' : algebraMap K (RatFunc K) (q.eval a) ∈ (placeOfPoint K a).toValuationSubring :=
    (placeOfPoint K a).algebraMap_mem' _
  have hsub : algebraMap K[X] (RatFunc K) q - algebraMap K (RatFunc K) (q.eval a)
      = algebraMap K[X] (RatFunc K) (q - C (q.eval a)) := by
    rw [map_sub, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  have hcongr : (placeOfPoint K a).evalAt (algebraMap K[X] (RatFunc K) q)
      = (placeOfPoint K a).evalAt (algebraMap K (RatFunc K) (q.eval a)) := by
    refine Place.evalAt_congr _ hmem hmem' ?_
    rw [hsub]
    rcases eq_or_ne (q - C (q.eval a)) 0 with h0 | h0
    · exact Or.inl (by rw [h0, map_zero])
    · refine Or.inr ?_
      rw [ord_placeOfPoint_algebraMap a h0]
      have hroot : (q - C (q.eval a)).IsRoot a := by
        simp only [IsRoot.def, eval_sub, eval_C, sub_self]
      exact_mod_cast (rootMultiplicity_pos h0).mpr hroot
  rw [hcongr, Place.evalAt_algebraMap]
