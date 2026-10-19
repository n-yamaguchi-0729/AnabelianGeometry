/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Nyll.AlgebraicCurves.FunctionFields.Rational.InstIsCurveOverRatFunc
import Nyll.AlgebraicCurves.FunctionFields.Extensions.CurveFiniteDimensionalAdjoinSimple
import Nyll.AlgebraicCurves.Divisors.Correspondences.Correspondences

/-! # The finite square extension in the already selected pair coordinate

The target field is literally a rational function field. Its root coordinate
is X, and the given pair function maps to X squared. Finiteness follows from
transcendence of X squared and the existing one-variable function-field theorem.
-/
noncomputable section
open AlgebraicCurve
open scoped RatFunc

namespace AnabelianGeometry.KummerTheory

/-- Substitution of X squared, with its image field supplied by transcendence. -/
def ratFuncSquareHom (k : Type) [Field k] : RatFunc k →ₐ[k] RatFunc k :=
  (IntermediateField.adjoin k ({(RatFunc.X : RatFunc k) ^ 2} : Set (RatFunc k))).val.comp
    (RatFunc.algEquivOfTranscendental ((RatFunc.X : RatFunc k) ^ 2)
      (RatFunc.transcendental_X.pow (by decide))).toAlgHom

@[simp]
theorem ratFuncSquareHom_X (k : Type) [Field k] :
    ratFuncSquareHom k RatFunc.X = (RatFunc.X : RatFunc k) ^ 2 := by
  exact RatFunc.algEquivOfTranscendental_X ((RatFunc.X : RatFunc k) ^ 2)
    (RatFunc.transcendental_X.pow (by decide))

/-- The square substitution is an actual finite field homomorphism. -/
theorem ratFuncSquareHom_finite (k : Type) [Field k] :
    (ratFuncSquareHom k).toRingHom.Finite := by
  let S := IntermediateField.adjoin k ({(RatFunc.X : RatFunc k) ^ 2} : Set (RatFunc k))
  let : IsCurveOver k (RatFunc k) := AlgebraicCurve.instIsCurveOverRatFunc k
  let : Algebra.EssFiniteType (Polynomial k) (RatFunc k) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial k))
  let : Algebra.EssFiniteType k (RatFunc k) :=
    Algebra.EssFiniteType.comp k (Polynomial k) (RatFunc k)
  let : FiniteDimensional S (RatFunc k) :=
    IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
      (RatFunc.transcendental_X.pow (show 0 < (2 : ℕ) from by decide))
  have hi : S.val.toRingHom.Finite := by
    change Module.Finite S (RatFunc k)
    infer_instance
  exact hi.comp (RatFunc.algEquivOfTranscendental ((RatFunc.X : RatFunc k) ^ 2)
    (RatFunc.transcendental_X.pow (by decide))).toRingEquiv.finite

/-- The same pair-coordinate equivalence is used contravariantly. -/
def ratFuncPairSquareHom {k : Type} [Field k]
    (eF : RatFunc k ≃ₐ[k] RatFunc k) : RatFunc k →ₐ[k] RatFunc k :=
  (ratFuncSquareHom k).comp eF.symm.toAlgHom

/-- The original function, without changing its scalar, is the square of X. -/
theorem ratFuncPairSquareHom_apply_pair
    {k : Type} [Field k] (eF : RatFunc k ≃ₐ[k] RatFunc k)
    (f : RatFunc k) (hf : eF RatFunc.X = f) :
    ratFuncPairSquareHom eF f = (RatFunc.X : RatFunc k) ^ 2 := by
  rw [← hf]
  change ratFuncSquareHom k (eF.symm (eF RatFunc.X)) = (RatFunc.X : RatFunc k) ^ 2
  rw [eF.symm_apply_apply, ratFuncSquareHom_X]

theorem ratFuncPairSquareHom_finite
    {k : Type} [Field k] (eF : RatFunc k ≃ₐ[k] RatFunc k) :
    (ratFuncPairSquareHom eF).toRingHom.Finite :=
  (ratFuncSquareHom_finite k).comp eF.symm.toRingEquiv.finite

/-- Integrality is proved from the actual finite square homomorphism. -/
theorem ratFuncPairSquareHom_isIntegral
    {k : Type} [Field k] (eF : RatFunc k ≃ₐ[k] RatFunc k) :
    (ratFuncPairSquareHom eF).toRingHom.IsIntegral :=
  (ratFuncPairSquareHom_finite eF).to_isIntegral

end AnabelianGeometry.KummerTheory
