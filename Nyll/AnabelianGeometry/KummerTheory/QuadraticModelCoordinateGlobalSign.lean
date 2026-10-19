/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.KummerTheory.RatFuncCoordinatePlaceUniqueness

/-! # One global quadratic model comparison acts on every finite label

A single rational-function-field automorphism fixing X squared sends X to X
or to negative X. The same alternative therefore controls all finite rational
places simultaneously. This is a global model-coordinate statement, rather
than an identification of independently chosen two-point fibres.
-/
noncomputable section
open AlgebraicCurve AlgebraicGeometry.ProjSpace

namespace AnabelianGeometry.KummerTheory

/-- Comparing the same quadratic root through two actual field coordinates
fixes its square whenever the coefficient of that square is unchanged. -/
theorem quadraticCoordinateComparison_fixes_square
    {A k : Type*} [CommRing A] [Field k]
    (e e' : A ≃+* RatFunc k) (root a : A) (hr : root ^ 2 = a)
    (he : e root = RatFunc.X) (ha : e' a = e a) :
    (e.symm.trans e') ((RatFunc.X : RatFunc k) ^ 2) = RatFunc.X ^ 2 := by
  have hea : e a = (RatFunc.X : RatFunc k) ^ 2 := by
    rw [← hr, map_pow, he]
  have hsa : e.symm ((RatFunc.X : RatFunc k) ^ 2) = a := by
    rw [← hea, e.symm_apply_apply]
  change e' (e.symm ((RatFunc.X : RatFunc k) ^ 2)) = RatFunc.X ^ 2
  rw [hsa, ha, hea]

private theorem hasValue_neg_of_hasValue
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (V : Place k F) {f : F} {a : k} (h : V.HasValue f a) :
    V.HasValue (-f) (-a) := by
  obtain ⟨hf, hv⟩ := h
  refine ⟨neg_mem hf, ?_⟩
  have heq : (⟨-f, neg_mem hf⟩ : V.toValuationSubring) = -⟨f, hf⟩ := rfl
  rw [heq, map_neg, hv, map_neg]

/-- One actual global coordinate comparison has one sign on every finite
rational label, including all omitted labels of the same model open. -/
theorem ratFunc_square_fixed_all_finite_places
    {k : Type} [Field k] (τ : RatFunc k ≃ₐ[k] RatFunc k)
    (hτ : τ ((RatFunc.X : RatFunc k) ^ 2) = RatFunc.X ^ 2) :
    let hInt : τ.toAlgHom.toRingHom.IsIntegral := τ.toRingEquiv.finite.to_isIntegral
    (∀ r : k, (RationalFunctionField.placeOfPoint k r).restrictAlong τ.toAlgHom hInt =
      RationalFunctionField.placeOfPoint k r) ∨
      ∀ r : k, (RationalFunctionField.placeOfPoint k r).restrictAlong τ.toAlgHom hInt =
        RationalFunctionField.placeOfPoint k (-r) := by
  intro hInt
  have hsq : τ (RatFunc.X : RatFunc k) ^ 2 = RatFunc.X ^ 2 :=
    (map_pow τ RatFunc.X 2).symm.trans hτ
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hX | hX
  · left
    intro r
    apply eq_placeOfPoint_of_hasValue_polynomial_X k _ r
    apply (Place.hasValue_restrictAlong_iff τ.toAlgHom hInt
      (RationalFunctionField.placeOfPoint k r)
      (algebraMap (Polynomial k) (RatFunc k) Polynomial.X) r).mpr
    simpa only [RatFunc.algebraMap_X, AlgEquiv.coe_toAlgHom, hX] using
      ratFunc_placeOfPoint_hasValue_X r
  · right
    intro r
    apply eq_placeOfPoint_of_hasValue_polynomial_X k _ (-r)
    apply (Place.hasValue_restrictAlong_iff τ.toAlgHom hInt
      (RationalFunctionField.placeOfPoint k r)
      (algebraMap (Polynomial k) (RatFunc k) Polynomial.X) (-r)).mpr
    simpa only [RatFunc.algebraMap_X, AlgEquiv.coe_toAlgHom, hX] using
      hasValue_neg_of_hasValue (RationalFunctionField.placeOfPoint k r)
        (ratFunc_placeOfPoint_hasValue_X r)

end AnabelianGeometry.KummerTheory
