/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # A prescribed generator gives a rational-function coordinate

These are purely algebraic constructors. Their inputs concern the same function
`f` as their output coordinate: no independent coordinate or preservation
assumption is introduced. In the geometric application, the hypotheses are
supplied by the full place-order formula for that function.
-/

noncomputable section

namespace AnabelianGeometry.KummerTheory

/-- A transcendental generator of `k(t)` is the image of `X` under a
`k`-algebra automorphism. -/
def ratFuncCoordinateOfAdjoinEqTop
    {k : Type*} [Field k]
    (f : RatFunc k) (hf : Transcendental k f)
    (hgen : IntermediateField.adjoin k {f} = ⊤) :
    RatFunc k ≃ₐ[k] RatFunc k :=
  (RatFunc.algEquivOfTranscendental f hf).trans
    ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv)

@[simp]
theorem ratFuncCoordinateOfAdjoinEqTop_apply_X
    {k : Type*} [Field k]
    (f : RatFunc k) (hf : Transcendental k f)
    (hgen : IntermediateField.adjoin k {f} = ⊤) :
    ratFuncCoordinateOfAdjoinEqTop f hf hgen RatFunc.X = f := by
  change ((RatFunc.algEquivOfTranscendental f hf) RatFunc.X : RatFunc k) = f
  exact RatFunc.algEquivOfTranscendental_X f hf

theorem ratFunc_exists_algEquiv_apply_X_of_adjoin_eq_top
    {k : Type*} [Field k]
    (f : RatFunc k) (hf : Transcendental k f)
    (hgen : IntermediateField.adjoin k {f} = ⊤) :
    ∃ e : RatFunc k ≃ₐ[k] RatFunc k, e RatFunc.X = f :=
  ⟨ratFuncCoordinateOfAdjoinEqTop f hf hgen,
    ratFuncCoordinateOfAdjoinEqTop_apply_X f hf hgen⟩

/-- The `finrank = 1` input already implies the generated subfield is all of
`k(t)`. No separate finite-dimensionality assumption is necessary. -/
theorem ratFunc_exists_algEquiv_apply_X_of_finrank_eq_one
    {k : Type*} [Field k]
    (f : RatFunc k) (hf : Transcendental k f)
    (hdegree : Module.finrank (IntermediateField.adjoin k {f}) (RatFunc k) = 1) :
    ∃ e : RatFunc k ≃ₐ[k] RatFunc k, e RatFunc.X = f := by
  apply ratFunc_exists_algEquiv_apply_X_of_adjoin_eq_top f hf
  exact IntermediateField.finrank_eq_one_iff_eq_top.mp hdegree

end AnabelianGeometry.KummerTheory
