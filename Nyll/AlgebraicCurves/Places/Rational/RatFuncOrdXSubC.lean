/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_ord_X_sub_C.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Rational.Classification
import Nyll.AlgebraicCurves.Places.Rational.RatFuncDegreeEqZeroEqOrdAlgebraMap

/-!
# Orders of a linear polynomial
-/

open Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField

open AlgebraicCurves.Places.Rational.Proofs in
open RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap in
theorem AlgebraicCurve.RationalFunctionField.ord_X_sub_C (K : Type*) [Field K] [DecidableEq
  (RatFunc K)] (b : K) (v : Place K (RatFunc K)) : v.ord (algebraMap (Polynomial K) (RatFunc K)
  (Polynomial.X - Polynomial.C b)) = (Finsupp.single (placeOfPoint K b) (1 : ℤ) + Finsupp.single
  (placeInfty K) (-1 : ℤ)) v := by
  have h :=
    AlgebraicCurve.RationalFunctionField.WFj.single_add_single_apply_eq_ord
      (placeInfty_ne_ofHeightOneSpectrum K) (irreducible_X_sub_C b) v
  rw [natDegree_X_sub_C, Nat.cast_one] at h
  exact h.symm
