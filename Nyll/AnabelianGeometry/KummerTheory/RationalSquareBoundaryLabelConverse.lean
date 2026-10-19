/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.KummerTheory.RatFuncCoordinatePlaceUniqueness
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticBoundaryFiniteLabels
import Nyll.AlgebraicCurves.Models.Ramification.OpenBoundary
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # The retained square-root labels belong to the actual omitted boundary

The model morphism is the original supplied p. Its original place clause and
the literal pullback range give both directions of boundary membership.
The selected finite root and its negative therefore give actual omitted places,
not merely a list that contains the omitted places.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AlgebraicCurve.CurveModel

/-- The original model-place clause identifies the entire actual pullback
boundary with the inverse image under the same restriction of places. -/
theorem openBoundaryPlaces_pullback_iff_restrictAlong
    {K F F' : Type} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F']
    (M : CurveModel K F) (N : CurveModel K F')
    (p : N.C ⟶ M.C) (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hplaces : ∀ y : closedPoints N.C,
      ∃ hy : p.base y.val ∈ closedPoints M.C,
        M.placeOfPoint ⟨p.base y.val, hy⟩ = (N.placeOfPoint y).restrictAlong φ hφ)
    {U : Scheme} (j : U ⟶ M.C) [IsOpenImmersion j]
    (W : Place K F') :
    W ∈ N.openBoundaryPlaces (pullback.fst p j) ↔
      W.restrictAlong φ hφ ∈ M.openBoundaryPlaces j := by
  let y := N.placeEquiv.symm W
  obtain ⟨hy, hplace⟩ := hplaces y
  have hyPlace : N.placeOfPoint y = W := by
    rw [← N.placeEquiv_apply]
    exact N.placeEquiv.apply_symm_apply W
  rw [hyPlace] at hplace
  change y.val ∉ Set.range (pullback.fst p j) ↔
    (M.placeEquiv.symm (W.restrictAlong φ hφ)).val ∉ Set.range j
  rw [← hplace, ← M.placeEquiv_apply, M.placeEquiv.symm_apply_apply,
    IsOpenImmersion.range_pullbackFst j p]
  change (p.base y.val ∉ Set.range j) ↔ p.base y.val ∉ Set.range j
  exact Iff.rfl

end AlgebraicCurve.CurveModel

namespace AnabelianGeometry.KummerTheory

/-- Exact equality of the original finite fibre with the two retained root
labels. This remains valid at zero, where the two labels coincide. -/
theorem ratFuncPairSquare_fiber_iff_root_or_neg
    {k : Type} [Field k]
    (e : RatFunc k ≃ₐ[k] RatFunc k) (f : RatFunc k) (hf : e RatFunc.X = f)
    (V W : Place k (RatFunc k)) (a r : k) (hr : r ^ 2 = a)
    (hV : V.HasValue f a) :
    W.restrictAlong (ratFuncPairSquareHom e) (ratFuncPairSquareHom_isIntegral e) = V ↔
      W = RationalFunctionField.placeOfPoint k r ∨
        W = RationalFunctionField.placeOfPoint k (-r) := by
  constructor
  · intro hw
    have h := Place.hasValue_of_restrictAlong_eq (ratFuncPairSquareHom e)
      (ratFuncPairSquareHom_isIntegral e) W V hw f a hV
    rw [ratFuncPairSquareHom_apply_pair e f hf] at h
    exact ratFunc_eq_standardPlace_of_hasValue_square W a r hr h
  · rintro (h | h)
    · rw [h]
      exact ratFuncPairSquare_restrict_placeOfPoint_root e f hf V a r hr hV
    · rw [h]
      exact ratFuncPairSquare_restrict_placeOfPoint_root e f hf V a (-r) (by simpa using hr) hV

/-- Both literal signs of a selected root belong to the boundary of the
same square-model open above the original finite-value target boundary place. -/
theorem rationalSquareModel_root_labels_mem_actual_boundary
    {k : Type} [Field k] {U : Scheme}
    (j : U ⟶ (projectiveLineRatFuncModel k).C) [IsOpenImmersion j]
    (p : (projectiveLineRatFuncModel k).C ⟶ (projectiveLineRatFuncModel k).C)
    (e : RatFunc k ≃ₐ[k] RatFunc k) (f : RatFunc k) (hf : e RatFunc.X = f)
    (hplaces : ∀ y : closedPoints (projectiveLineRatFuncModel k).C,
      ∃ hy : p.base y.val ∈ closedPoints (projectiveLineRatFuncModel k).C,
        (projectiveLineRatFuncModel k).placeOfPoint ⟨p.base y.val, hy⟩ =
          ((projectiveLineRatFuncModel k).placeOfPoint y).restrictAlong
            (ratFuncPairSquareHom e) (ratFuncPairSquareHom_isIntegral e))
    (V : (projectiveLineRatFuncModel k).openBoundaryPlaces j)
    (a r : k) (hr : r ^ 2 = a) (hV : V.val.HasValue f a) :
    RationalFunctionField.placeOfPoint k r ∈
        (projectiveLineRatFuncModel k).openBoundaryPlaces (pullback.fst p j) ∧
      RationalFunctionField.placeOfPoint k (-r) ∈
        (projectiveLineRatFuncModel k).openBoundaryPlaces (pullback.fst p j) := by
  have hroot (z : k) (hz : z ^ 2 = a) :
      RationalFunctionField.placeOfPoint k z ∈
        (projectiveLineRatFuncModel k).openBoundaryPlaces (pullback.fst p j) := by
    apply (CurveModel.openBoundaryPlaces_pullback_iff_restrictAlong
      (projectiveLineRatFuncModel k) (projectiveLineRatFuncModel k) p
      (ratFuncPairSquareHom e) (ratFuncPairSquareHom_isIntegral e)
      hplaces j (RationalFunctionField.placeOfPoint k z)).mpr
    rw [ratFuncPairSquare_restrict_placeOfPoint_root e f hf V.val a z hz hV]
    exact V.property
  exact ⟨hroot r hr, hroot (-r) (by simpa using hr)⟩

end AnabelianGeometry.KummerTheory
