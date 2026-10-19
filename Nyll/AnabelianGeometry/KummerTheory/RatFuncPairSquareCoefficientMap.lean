/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationFiniteExtensionCoordinate
import Nyll.AlgebraicCurves.FunctionFields.Rational.RatFuncPairSquareMap

/-! # The same pair-square map commutes with the original coefficient extension

The square substitution and the already compatible pair coordinates determine
the full field square. Conjugating by the literal projective model's field
identifications gives the corresponding square of actual function-field maps.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped Polynomial RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AnabelianGeometry.KummerTheory

private theorem squareRatFuncHom_eq_of_C_X
    {k L : Type*} [Field k] [Field L] (φ ψ : RatFunc k →+* L)
    (hC : ∀ c : k, φ (RatFunc.C c) = ψ (RatFunc.C c))
    (hX : φ RatFunc.X = ψ RatFunc.X) : φ = ψ := by
  have hpoly (p : Polynomial k) :
      φ (algebraMap (Polynomial k) (RatFunc k) p) =
        ψ (algebraMap (Polynomial k) (RatFunc k) p) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
    | monomial n c =>
      rw [RatFunc.algebraMap_monomial]
      simpa only [map_mul, map_pow] using
        congrArg₂ (· * ·) (hC c) (congrArg (· ^ n) hX)
  apply RingHom.ext
  intro z
  induction z using RatFunc.induction_on with
  | f p q _hq =>
    simpa only [map_div₀] using congrArg₂ (· / ·) (hpoly p) (hpoly q)

/-- Substitution by X squared commutes with the actual coefficient map. -/
theorem ratFuncSquareHom_coefficient_commute
    (k E : Type) [Field k] [Field E] [Algebra k E] :
    ∀ z : RatFunc k,
      ratFuncSquareHom E (algebraMap (RatFunc k) (RatFunc E) z) =
        algebraMap (RatFunc k) (RatFunc E) (ratFuncSquareHom k z) := by
  have hcoeff (c : k) :
      algebraMap (RatFunc k) (RatFunc E) (algebraMap k (RatFunc k) c) =
        algebraMap E (RatFunc E) (algebraMap k E c) :=
    (IsScalarTower.algebraMap_apply k (RatFunc k) (RatFunc E) c).symm.trans
      (IsScalarTower.algebraMap_apply k E (RatFunc E) c)
  have hmap := squareRatFuncHom_eq_of_C_X
    ((ratFuncSquareHom E).toRingHom.comp (algebraMap (RatFunc k) (RatFunc E)))
    ((algebraMap (RatFunc k) (RatFunc E)).comp (ratFuncSquareHom k).toRingHom)
    (fun c => by
      change ratFuncSquareHom E (algebraMap (RatFunc k) (RatFunc E) (RatFunc.C c)) =
        algebraMap (RatFunc k) (RatFunc E) (ratFuncSquareHom k (RatFunc.C c))
      rw [← RatFunc.algebraMap_eq_C, (ratFuncSquareHom k).commutes,
        hcoeff, (ratFuncSquareHom E).commutes])
    (by
      change ratFuncSquareHom E (algebraMap (RatFunc k) (RatFunc E) RatFunc.X) =
        algebraMap (RatFunc k) (RatFunc E) (ratFuncSquareHom k RatFunc.X)
      rw [ratFunc_constantExtension_map_X, ratFuncSquareHom_X,
        ratFuncSquareHom_X, map_pow, ratFunc_constantExtension_map_X])
  exact DFunLike.congr_fun hmap

/-- The original square map and the same-function E-square map commute on
all field elements, including the inverse coordinate used contravariantly. -/
theorem ratFuncPairSquareHom_coefficient_commute
    {k E : Type} [Field k] [Field E] [Algebra k E]
    (e : RatFunc k ≃ₐ[k] RatFunc k) (eE : RatFunc E ≃ₐ[E] RatFunc E)
    (f : RatFunc k) (he : e RatFunc.X = f)
    (heE : eE RatFunc.X = algebraMap (RatFunc k) (RatFunc E) f) :
    ∀ z : RatFunc k,
      ratFuncPairSquareHom eE (algebraMap (RatFunc k) (RatFunc E) z) =
        algebraMap (RatFunc k) (RatFunc E) (ratFuncPairSquareHom e z) := by
  have hsymm (z : RatFunc k) :
      eE.symm (algebraMap (RatFunc k) (RatFunc E) z) =
        algebraMap (RatFunc k) (RatFunc E) (e.symm z) := by
    apply eE.injective
    rw [eE.apply_symm_apply, ratFunc_coordinates_coefficient_commute e eE f he heE,
      e.apply_symm_apply]
  intro z
  change ratFuncSquareHom E (eE.symm (algebraMap (RatFunc k) (RatFunc E) z)) =
    algebraMap (RatFunc k) (RatFunc E) (ratFuncSquareHom k (e.symm z))
  rw [hsymm, ratFuncSquareHom_coefficient_commute]

end AnabelianGeometry.KummerTheory

namespace AlgebraicGeometry.ProjSpace

open AnabelianGeometry.KummerTheory

-- The integral instance from ProjectiveLineRatFuncBaseChange is file-local.
-- Register the literal owner before elaborating the function-field square.
local instance pairSquareCoefficient_projectiveLine_integral
    (F : Type) [Field F] :
    IsIntegral (Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) F)) :=
  projectiveSpace_isIntegral F 1

/-- The pair-square endomorphisms in the literal projective models' function
fields form a commuting square with the actual projective coefficient map. -/
theorem ratFuncPairSquareHom_model_coefficient_square
    (k E : Type) [Field k] [Field E] [Algebra k E]
    (e : RatFunc k ≃ₐ[k] RatFunc k) (eE : RatFunc E ≃ₐ[E] RatFunc E)
    (f : RatFunc k) (he : e RatFunc.X = f)
    (heE : eE RatFunc.X = algebraMap (RatFunc k) (RatFunc E) f) :
    ((show (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel k).C
        from map k E 1).functionFieldMap (projectiveLineMap_denseRange k E)).comp
      ((projectiveLineRatFuncModel k).ffEquiv.toRingHom.comp
        ((ratFuncPairSquareHom e).toRingHom.comp
          (projectiveLineRatFuncModel k).ffEquiv.symm.toRingHom)) =
    ((projectiveLineRatFuncModel E).ffEquiv.toRingHom.comp
      ((ratFuncPairSquareHom eE).toRingHom.comp
        (projectiveLineRatFuncModel E).ffEquiv.symm.toRingHom)).comp
      ((show (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel k).C
        from map k E 1).functionFieldMap (projectiveLineMap_denseRange k E)) := by
  let M : CurveModel k (RatFunc k) := projectiveLineRatFuncModel k
  let N : CurveModel E (RatFunc E) := projectiveLineRatFuncModel E
  let φ : M.C.functionField →+* N.C.functionField :=
    (show N.C ⟶ M.C from map k E 1).functionFieldMap
      (projectiveLineMap_denseRange k E)
  have hcoeff (z : RatFunc k) :
      φ (M.ffEquiv z) = N.ffEquiv (algebraMap (RatFunc k) (RatFunc E) z) :=
    projectiveLineRatFuncEquiv_coefficientMap k E z
  apply RingHom.ext
  intro z
  change φ (M.ffEquiv (ratFuncPairSquareHom e (M.ffEquiv.symm z))) =
    N.ffEquiv (ratFuncPairSquareHom eE (N.ffEquiv.symm (φ z)))
  have hinv : N.ffEquiv.symm (φ z) =
      algebraMap (RatFunc k) (RatFunc E) (M.ffEquiv.symm z) := by
    apply N.ffEquiv.injective
    rw [N.ffEquiv.apply_symm_apply, ← hcoeff, M.ffEquiv.apply_symm_apply]
  rw [hcoeff, hinv, ratFuncPairSquareHom_coefficient_commute e eE f he heE]

end AlgebraicGeometry.ProjSpace
