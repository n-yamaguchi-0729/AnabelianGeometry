/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.CommonFiniteRationalModels
import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricGenus

/-! # Finite rational models from geometric genus and boundary size

The literal geometric function fields supply the curve models. The caller
provides the original compactifications and opens, their geometric genera,
and the number of geometric boundary points; no coordinate or model is input.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace AlgebraicGeometry.SmoothProperCurve
open AnabelianGeometry.ArithmeticIsomorphisms

namespace AnabelianGeometry.GeometricFundamentalGroup

private theorem boundary_card_eq_closed_complement
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) (V : M.C.Opens) :
    Nat.card (M.openBoundaryPlaces V.ι) =
      Nat.card {x : closedPoints M.C // x.val ∉ V} := by
  apply Nat.card_congr
  exact M.placeEquiv.symm.subtypeEquiv (fun p => by
    change (M.placeEquiv.symm p).val ∉ Set.range V.ι ↔
      (M.placeEquiv.symm p).val ∉ V
    rw [Scheme.Opens.range_ι]
    rfl)

/-- Both native constant covers become rational configurations over one
finite Galois extension, with the ambient and coefficient maps retained.
Only geometric genus and the actual geometric boundary size are required. -/
theorem exists_common_rational_models_of_geometricGenus_zero
    (k : Type) [Field k] [NumberField k]
    {C₁ C₂ : Scheme}
    (c₁ : C₁ ⟶ Spec (.of k)) (c₂ : C₂ ⟶ Spec (.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (U₁ : C₁.Opens) (U₂ : C₂.Opens)
    (hU₁ : (U₁ : Set C₁).Nonempty) (hU₂ : (U₂ : Set C₂).Nonempty)
    (hg₁ : geometricGenus k c₁ = 0) (hg₂ : geometricGenus k c₂ = 0)
    (hr₁ : 3 ≤ Nat.card
      {x : closedPoints (pullback c₁ (specMap k (AlgebraicClosure k)) : Scheme) //
        x.val ∉ pullback.fst c₁ (specMap k (AlgebraicClosure k)) ⁻¹ᵁ U₁})
    (hr₂ : 3 ≤ Nat.card
      {x : closedPoints (pullback c₂ (specMap k (AlgebraicClosure k)) : Scheme) //
        x.val ∉ pullback.fst c₂ (specMap k (AlgebraicClosure k)) ⁻¹ᵁ U₂}) :
    ∃ E : FiniteGaloisIntermediateField k (AlgebraicClosure k),
      ∃ s t : Finset (Projectivization E (E × E)),
        3 ≤ s.card ∧ 3 ≤ t.card ∧
        ∃ (I₁ : pullback c₁ (specMap k E) ≅ (projectiveLineRatFuncModel E).C)
          (I₂ : pullback c₂ (specMap k E) ≅ (projectiveLineRatFuncModel E).C),
          I₁.hom ≫ (projectiveLineRatFuncModel E).toBase =
            pullback.snd c₁ (specMap k E) ∧
          I₂.hom ≫ (projectiveLineRatFuncModel E).toBase =
            pullback.snd c₂ (specMap k E) ∧
        ∃ (Js : pullback (specMap k E) (U₁.ι ≫ c₁) ≅
            (rationalConfigurationOpen s : Scheme))
          (Jt : pullback (specMap k E) (U₂.ι ≫ c₂) ≅
            (rationalConfigurationOpen t : Scheme)),
          Js.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
            pullback.fst (specMap k E) (U₁.ι ≫ c₁) ∧
          Jt.hom ≫ ((rationalConfigurationOpen t).ι ≫ π E 1) =
            pullback.fst (specMap k E) (U₂.ι ≫ c₂) ∧
          Js.hom ≫ (rationalConfigurationOpen s).ι =
            (openBaseChangeIso c₁ (specMap k E) U₁).hom ≫
              (pullback.fst c₁ (specMap k E) ⁻¹ᵁ U₁).ι ≫ I₁.hom ∧
          Jt.hom ≫ (rationalConfigurationOpen t).ι =
            (openBaseChangeIso c₂ (specMap k E) U₂).hom ≫
              (pullback.fst c₂ (specMap k E) ⁻¹ᵁ U₂).ι ≫ I₂.hom := by
  let κ := AlgebraicClosure k
  let φ := specMap k κ
  let D₁ := pullback c₁ φ
  let D₂ := pullback c₂ φ
  let d₁ : D₁ ⟶ Spec (.of κ) := pullback.snd c₁ φ
  let d₂ : D₂ ⟶ Spec (.of κ) := pullback.snd c₂ φ
  have : IsIntegral C₁ := GeometricallyIntegral.isIntegral_of_subsingleton c₁
  have : IsIntegral C₂ := GeometricallyIntegral.isIntegral_of_subsingleton c₂
  let : Algebra κ D₁.functionField := (baseToFunctionField d₁).toAlgebra
  let : Algebra κ D₂.functionField := (baseToFunctionField d₂).toAlgebra
  let : Algebra k D₁.functionField :=
    ((algebraMap κ D₁.functionField).comp (algebraMap k κ)).toAlgebra
  let : Algebra k D₂.functionField :=
    ((algebraMap κ D₂.functionField).comp (algebraMap k κ)).toAlgebra
  have : IsScalarTower k κ D₁.functionField := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k κ D₂.functionField := IsScalarTower.of_algebraMap_eq' rfl
  let M₁ : CurveModel κ D₁.functionField := literalCurveModel d₁
  let M₂ : CurveModel κ D₂.functionField := literalCurveModel d₂
  obtain ⟨hcurve₁, hfinite₁⟩ := literalCurveModel_functionField_properties d₁
  obtain ⟨hcurve₂, hfinite₂⟩ := literalCurveModel_functionField_properties d₂
  have : IsCurveOver κ D₁.functionField := hcurve₁
  have : IsCurveOver κ D₂.functionField := hcurve₂
  have : Algebra.EssFiniteType κ D₁.functionField := hfinite₁
  have : Algebra.EssFiniteType κ D₂.functionField := hfinite₂
  have hgenus₁ : genusFF κ D₁.functionField = 0 := hg₁
  have hgenus₂ : genusFF κ D₂.functionField = 0 := hg₂
  have hboundary₁ : 3 ≤ Nat.card (M₁.openBoundaryPlaces
      ((pullback.fst c₁ φ ⁻¹ᵁ U₁).ι)) := by
    exact (boundary_card_eq_closed_complement M₁
      (show M₁.C.Opens from pullback.fst c₁ φ ⁻¹ᵁ U₁)).symm ▸ hr₁
  have hboundary₂ : 3 ≤ Nat.card (M₂.openBoundaryPlaces
      ((pullback.fst c₂ φ ⁻¹ᵁ U₂).ι)) := by
    exact (boundary_card_eq_closed_complement M₂
      (show M₂.C.Opens from pullback.fst c₂ φ ⁻¹ᵁ U₂)).symm ▸ hr₂
  have : _root_.IsGalois k κ := inferInstance
  exact exists_common_finiteGalois_rationalConfiguration_models M₁ M₂ c₁ c₂
    (Iso.refl _) (Iso.refl _) (Category.id_comp _) (Category.id_comp _)
    hgenus₁ hgenus₂ U₁ U₂ hU₁ hU₂
    ((congrArg (fun f : M₁.C ⟶ C₁ =>
      3 ≤ Nat.card (M₁.openBoundaryPlaces (f ⁻¹ᵁ U₁).ι))
      (Category.id_comp (show M₁.C ⟶ C₁ from pullback.fst c₁ φ))).mpr hboundary₁)
    ((congrArg (fun f : M₂.C ⟶ C₂ =>
      3 ≤ Nat.card (M₂.openBoundaryPlaces (f ⁻¹ᵁ U₂).ι))
      (Category.id_comp (show M₂.C ⟶ C₂ from pullback.fst c₂ φ))).mpr hboundary₂)

end AnabelianGeometry.GeometricFundamentalGroup
