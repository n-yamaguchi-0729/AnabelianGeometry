/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Places.Evaluation.PlaceValueRestrictAlong
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineStandardPlace
import Nyll.AlgebraicCurves.FunctionFields.Rational.RatFuncPairSquareMap
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Uniqueness of the place at a value of the unchanged rational coordinate

Restriction along the given coordinate equivalence is injective. Therefore a
finite value of its original image of X determines the place, and the selected
square-root labels restrict to the original target place with that value.
-/
noncomputable section
open AlgebraicCurve AlgebraicGeometry.ProjSpace
open scoped RatFunc

namespace AlgebraicCurve.Place

/-- Restriction along an actual field equivalence is injective on places. -/
theorem restrictAlong_algEquiv_injective
    {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F']
    (e : F ≃ₐ[K] F') (he : e.toAlgHom.toRingHom.IsIntegral) :
    Function.Injective (fun V : Place K F' => V.restrictAlong e.toAlgHom he) := by
  intro V W h
  change V.restrictAlong e.toAlgHom he = W.restrictAlong e.toAlgHom he at h
  apply Place.ext
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  have hmem : y ∈ (V.restrictAlong e.toAlgHom he).toValuationSubring ↔
      y ∈ (W.restrictAlong e.toAlgHom he).toValuationSubring := by rw [h]
  exact hmem

end AlgebraicCurve.Place

namespace AnabelianGeometry.KummerTheory

variable {k : Type} [Field k]

/-- Two places with the same finite value of the given rational coordinate
are equal. No rationality assumption is required on either place. -/
theorem ratFunc_place_eq_of_hasValue_coordinate
    (e : RatFunc k ≃ₐ[k] RatFunc k) (f : RatFunc k) (hf : e RatFunc.X = f)
    (V W : Place k (RatFunc k)) (a : k)
    (hV : V.HasValue f a) (hW : W.HasValue f a) : V = W := by
  have he : e.toAlgHom.toRingHom.IsIntegral :=
    e.toRingEquiv.finite.to_isIntegral
  have hstandard (T : Place k (RatFunc k)) (hT : T.HasValue f a) :
      T.restrictAlong e.toAlgHom he = RationalFunctionField.placeOfPoint k a := by
    apply eq_placeOfPoint_of_hasValue_polynomial_X k _ a
    apply (Place.hasValue_restrictAlong_iff e.toAlgHom he T
      (algebraMap (Polynomial k) (RatFunc k) Polynomial.X) a).mpr
    simpa only [RatFunc.algebraMap_X, AlgEquiv.coe_toAlgHom, hf] using hT
  apply Place.restrictAlong_algEquiv_injective e he
  exact (hstandard V hV).trans (hstandard W hW).symm

/-- The standard finite place has the literal value of the standard root
coordinate, as proved on the original projective-line chart. -/
theorem ratFunc_placeOfPoint_hasValue_X (r : k) :
    (RationalFunctionField.placeOfPoint k r).HasValue (RatFunc.X : RatFunc k) r := by
  have hv : (r, (1 : k)) ≠ 0 := fun h => one_ne_zero (congrArg Prod.snd h)
  have he := literalRationalPuncturePlace_eq_placeOfPoint k (r, 1) hv one_ne_zero
  simp only [div_one] at he
  have h := literalRationalPuncturePlace_hasValue_X k (r, 1) hv one_ne_zero
  simpa only [he, RatFunc.algebraMap_X, div_one] using h

/-- The standard place at the selected root lies over the original target
place at its original finite value under the unchanged pair-square map. -/
theorem ratFuncPairSquare_restrict_placeOfPoint_root
    (e : RatFunc k ≃ₐ[k] RatFunc k) (f : RatFunc k) (hf : e RatFunc.X = f)
    (V : Place k (RatFunc k)) (a r : k) (hr : r ^ 2 = a)
    (hV : V.HasValue f a) :
    (RationalFunctionField.placeOfPoint k r).restrictAlong
      (ratFuncPairSquareHom e) (ratFuncPairSquareHom_isIntegral e) = V := by
  apply ratFunc_place_eq_of_hasValue_coordinate e f hf _ V a _ hV
  apply (Place.hasValue_restrictAlong_iff (ratFuncPairSquareHom e)
    (ratFuncPairSquareHom_isIntegral e) (RationalFunctionField.placeOfPoint k r) f a).mpr
  rw [ratFuncPairSquareHom_apply_pair e f hf]
  have h := ratFunc_placeOfPoint_hasValue_X r
  simpa only [← pow_two, hr] using h.mul h

/-- Both signs of the already selected root lie over that same original
target place. They have not been chosen afresh from the fibre. -/
theorem ratFuncPairSquare_restrict_placeOfPoint_root_and_neg
    (e : RatFunc k ≃ₐ[k] RatFunc k) (f : RatFunc k) (hf : e RatFunc.X = f)
    (V : Place k (RatFunc k)) (a r : k) (hr : r ^ 2 = a)
    (hV : V.HasValue f a) :
    (RationalFunctionField.placeOfPoint k r).restrictAlong
        (ratFuncPairSquareHom e) (ratFuncPairSquareHom_isIntegral e) = V ∧
      (RationalFunctionField.placeOfPoint k (-r)).restrictAlong
        (ratFuncPairSquareHom e) (ratFuncPairSquareHom_isIntegral e) = V := by
  exact ⟨ratFuncPairSquare_restrict_placeOfPoint_root e f hf V a r hr hV,
    ratFuncPairSquare_restrict_placeOfPoint_root e f hf V a (-r) (by simpa using hr) hV⟩

end AnabelianGeometry.KummerTheory
