/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.AlgebraicCurves.Places.Evaluation.Value
import Nyll.AlgebraicCurves.Places.Basic

/-! # The literal residue value at a rational place with nonnegative order -/
noncomputable section
namespace AlgebraicCurve.Place

/-- At a rational place, the literal evaluation is the residue value of every
nonzero function with nonnegative order. -/
theorem hasValue_evalAt_of_ord_nonneg
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (V : Place k F) (hV : V.IsRational) (f : F) (hf : f ≠ 0)
    (hreg : 0 ≤ V.ord f) : V.HasValue f (V.evalAt f) := by
  have hmem := (V.mem_iff_ord_nonneg hf).mpr hreg
  exact ⟨hmem, (V.algebraMap_evalAt hV hmem).symm⟩

/-- No new value is selected: the finite alternative uses the original evalAt. -/
theorem ord_neg_or_hasValue_evalAt
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (V : Place k F) (hV : V.IsRational) (f : F) (hf : f ≠ 0) :
    V.ord f < 0 ∨ V.HasValue f (V.evalAt f) := by
  by_cases h : V.ord f < 0
  · exact Or.inl h
  · exact Or.inr (V.hasValue_evalAt_of_ord_nonneg hV f hf (le_of_not_gt h))

end AlgebraicCurve.Place
