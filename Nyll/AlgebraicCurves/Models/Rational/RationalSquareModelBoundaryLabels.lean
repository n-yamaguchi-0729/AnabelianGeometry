/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.FunctionFields.Rational.RatFuncPairSquareMap
import Nyll.AlgebraicCurves.Places.Rational.RatFuncSquareFibers
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineRatFuncModel
import Nyll.AlgebraicCurves.Places.Evaluation.PlaceValueRestrictAlong
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Actual omitted-place labels on the rational square model

For the literal inverse-image open, every omitted source place lies above an
omitted target place. The retained model-map place clause transfers the given
pair function's values and poles to X squared. The selected root labels then
exhaust the actual source boundary and prove its rationality.
-/
noncomputable section
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AnabelianGeometry.KummerTheory

/-- The original p-place compatibility and actual target values supply labels
for every omitted place of the literal square-model open. -/
theorem rationalSquareModel_actual_boundary_labels
    {k : Type} [Field k] {ι : Type}
    {U : Scheme} (j : U ⟶ (projectiveLineRatFuncModel k).C) [IsOpenImmersion j]
    (p : (projectiveLineRatFuncModel k).C ⟶ (projectiveLineRatFuncModel k).C)
    (eF : RatFunc k ≃ₐ[k] RatFunc k) (f : RatFunc k) (hf : eF RatFunc.X = f)
    (v r : ι → k) (hr : ∀ i, r i ^ 2 = v i)
    (hplaces : ∀ y : closedPoints (projectiveLineRatFuncModel k).C,
      ∃ hy : p.base y.val ∈ closedPoints (projectiveLineRatFuncModel k).C,
        (projectiveLineRatFuncModel k).placeOfPoint ⟨p.base y.val, hy⟩ =
          ((projectiveLineRatFuncModel k).placeOfPoint y).restrictAlong
            (ratFuncPairSquareHom eF) (ratFuncPairSquareHom_isIntegral eF))
    (hvalues : ∀ V : (projectiveLineRatFuncModel k).openBoundaryPlaces j,
      V.val.ord f < 0 ∨ ∃ i, V.val.HasValue f (v i)) :
    ∀ W : (projectiveLineRatFuncModel k).openBoundaryPlaces (pullback.fst p j),
      W.val.IsRational ∧
        (W.val = RationalFunctionField.placeInfty k ∨
          ∃ i, W.val = RationalFunctionField.placeOfPoint k (r i) ∨
            W.val = RationalFunctionField.placeOfPoint k (-(r i))) := by
  intro W
  let M := projectiveLineRatFuncModel k
  let y := M.placeEquiv.symm W.val
  obtain ⟨hy, hplace⟩ := hplaces y
  let V := M.placeOfPoint ⟨p.base y.val, hy⟩
  have hyPlace : M.placeOfPoint y = W.val := by
    rw [← M.placeEquiv_apply]
    exact M.placeEquiv.apply_symm_apply W.val
  have hrestrict : W.val.restrictAlong (ratFuncPairSquareHom eF)
      (ratFuncPairSquareHom_isIntegral eF) = V := by
    rw [hyPlace] at hplace
    exact hplace.symm
  have hV : V ∈ M.openBoundaryPlaces j := by
    change (M.placeEquiv.symm (M.placeOfPoint ⟨p.base y.val, hy⟩)).val ∉ Set.range j
    rw [← M.placeEquiv_apply, M.placeEquiv.symm_apply_apply]
    intro hmem
    apply W.property
    change y.val ∈ Set.range (pullback.fst p j)
    rw [IsOpenImmersion.range_pullbackFst j p]
    exact hmem
  have hrootValues : W.val.ord ((RatFunc.X : RatFunc k) ^ 2) < 0 ∨
      ∃ i, W.val.HasValue ((RatFunc.X : RatFunc k) ^ 2) (v i) := by
    rcases hvalues ⟨V, hV⟩ with h | ⟨i, h⟩
    · left
      have h' := Place.ord_neg_of_restrictAlong_eq (ratFuncPairSquareHom eF)
        (ratFuncPairSquareHom_isIntegral eF) W.val V hrestrict f h
      rwa [ratFuncPairSquareHom_apply_pair eF f hf] at h'
    · right
      refine ⟨i, ?_⟩
      have h' := Place.hasValue_of_restrictAlong_eq (ratFuncPairSquareHom eF)
        (ratFuncPairSquareHom_isIntegral eF) W.val V hrestrict f (v i) h
      rwa [ratFuncPairSquareHom_apply_pair eF f hf] at h'
  exact ⟨ratFunc_isRational_of_square_boundary v r hr W.val hrootValues,
    ratFunc_eq_standardPlace_of_square_boundary v r hr W.val hrootValues⟩

end AnabelianGeometry.KummerTheory
