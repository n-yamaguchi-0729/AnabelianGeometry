/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_evalAt_placeInfty_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Rational.InfinityArithmetic
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.Places.Evaluation.EvalAtCongr
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Evaluation at infinity from negative degree
-/

open Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField

namespace AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_evalAt_placeInfty_eq

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]

private theorem mem_placeInfty_of_intDegree_nonpos {f : RatFunc K} (hf : f ≠ 0)
    (h : f.intDegree ≤ 0) : f ∈ (placeInfty K).toValuationSubring :=
  (placeInfty K).mem_of_ord_nonneg hf (by rw [ord_placeInfty hf]; omega)

theorem _root_.AlgebraicCurve.RationalFunctionField.evalAt_placeInfty_eq (K : Type*) [Field K]
  [DecidableEq (RatFunc K)] {f : RatFunc K} {c : K} (h : f - algebraMap K (RatFunc K) c = 0 ∨ (f -
  algebraMap K (RatFunc K) c).intDegree < 0) : (placeInfty K).evalAt f = c := by
  have hsubmem : f - algebraMap K (RatFunc K) c ∈ (placeInfty K).toValuationSubring := by
    rcases h with h | h
    · rw [h]; exact zero_mem _
    · refine mem_placeInfty_of_intDegree_nonpos ?_ h.le
      intro h0
      rw [h0] at h
      simp only [RatFunc.intDegree_zero, lt_self_iff_false] at h
  have hmem : f ∈ (placeInfty K).toValuationSubring := by
    have : f = (f - algebraMap K (RatFunc K) c) + algebraMap K (RatFunc K) c := by ring
    rw [this]
    exact add_mem hsubmem ((placeInfty K).algebraMap_mem' c)
  have hcongr : (placeInfty K).evalAt f
      = (placeInfty K).evalAt (algebraMap K (RatFunc K) c) := by
    refine Place.evalAt_congr _ hmem ((placeInfty K).algebraMap_mem' c) ?_
    rcases h with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      have hne : f - algebraMap K (RatFunc K) c ≠ 0 := by
        intro h0
        rw [h0] at h
        simp only [RatFunc.intDegree_zero, lt_self_iff_false] at h
      rw [ord_placeInfty hne]
      omega
  rw [hcongr, Place.evalAt_algebraMap]

end AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_evalAt_placeInfty_eq
