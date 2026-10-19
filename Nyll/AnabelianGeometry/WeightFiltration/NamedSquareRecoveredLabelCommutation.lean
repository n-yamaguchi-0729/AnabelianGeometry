/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareChosenLabelInertia
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareInertiaNontriviality
import Nyll.AnabelianGeometry.WeightFiltration.LiftedPunctureProjection

/-! # Recovered label commutation for named square models -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups EtaleFundamentalGroups.Inertia
open CategoryTheory.PreGaloisCategory AnabelianGeometry.KummerTheory
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AnabelianGeometry.WeightFiltration

theorem namedSquare_recovered_label_projection_commutes
    (k E κ : Type) [Field k] [Field E] [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k κ] [Algebra E κ] [Infinite k] [Infinite E]
    (sS sT : Finset (Projectivization k (k × k)))
    (tS tT : Finset (Projectivization E (E × E)))
    (hsT : 3 ≤ sT.card) (htS : 3 ≤ tS.card)
    [IsNormalIntegral (rationalConfigurationGeometricScheme k κ sS)]
    [IsLocallyNoetherian (rationalConfigurationGeometricScheme k κ sS)]
    [ConnectedSpace (rationalConfigurationGeometricScheme k κ sS)]
    (ΩS : Type) [Field ΩS] [IsAlgClosed ΩS] [IsSepClosed ΩS]
    [Algebra (rationalConfigurationGeometricScheme k κ sS).functionField ΩS]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ sS).functionField ΩS]
    (WS : FiniteEtale (rationalConfigurationGeometricScheme k κ sS)) [IsConnected WS]
    (wS : (fiber ((rationalConfigurationGeometricScheme k κ sS).genericExtensionMorphism ΩS)).obj
      WS)
    (JS : WS.left ≅ rationalConfigurationGeometricScheme E κ tS)
    (qS : rationalConfigurationGeometricScheme E κ tS ⟶ rationalConfigurationGeometricScheme k κ sS)
    (hJS : JS.hom ≫ qS = WS.hom)
    (pS : (projectiveLineRatFuncModel κ).C ⟶ (projectiveLineRatFuncModel κ).C)
    (eS : RatFunc κ ≃ₐ[κ] RatFunc κ)
    (hplacesS : ∀ y : closedPoints (projectiveLineRatFuncModel κ).C,
      ∃ hy : pS.base y.val ∈ closedPoints (projectiveLineRatFuncModel κ).C,
        (projectiveLineRatFuncModel κ).placeOfPoint ⟨pS.base y.val, hy⟩ =
          ((projectiveLineRatFuncModel κ).placeOfPoint y).restrictAlong
            (ratFuncPairSquareHom eS) (ratFuncPairSquareHom_isIntegral eS))
    (hboundaryS : ∀ y : (projectiveLineRatFuncModel κ).C,
      y ∉ Set.range (rationalConfigurationBaseChangeChart E κ tS) ↔
        pS y ∉ Set.range (rationalConfigurationBaseChangeChart k κ sS))
    (hfieldS :
      let _hWIntegral : IsIntegral WS.left := isIntegral_left_of_isConnected_finiteEtale WS
      let _AKL : Algebra (rationalConfigurationGeometricScheme k κ sS).functionField
        WS.left.functionField :=
        finiteEtaleFunctionFieldAlgebra WS
      ∀ z : RatFunc κ,
        JS.hom.functionFieldMap JS.hom.homeomorph.surjective.denseRange
          (rationalConfigurationGeometricFunctionFieldEquiv E κ tS (ratFuncPairSquareHom eS z)) =
          algebraMap (rationalConfigurationGeometricScheme k κ sS).functionField
            WS.left.functionField
            (rationalConfigurationGeometricFunctionFieldEquiv k κ sS z))
    [IsNormalIntegral (rationalConfigurationGeometricScheme k κ sT)]
    [IsLocallyNoetherian (rationalConfigurationGeometricScheme k κ sT)]
    [ConnectedSpace (rationalConfigurationGeometricScheme k κ sT)]
    (ΩT : Type) [Field ΩT] [IsAlgClosed ΩT] [IsSepClosed ΩT]
    [Algebra (rationalConfigurationGeometricScheme k κ sT).functionField ΩT]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ sT).functionField ΩT]
    (WT : FiniteEtale (rationalConfigurationGeometricScheme k κ sT)) [IsConnected WT]
    (wT : (fiber ((rationalConfigurationGeometricScheme k κ sT).genericExtensionMorphism ΩT)).obj
      WT)
    (JT : WT.left ≅ rationalConfigurationGeometricScheme E κ tT)
    (qT : rationalConfigurationGeometricScheme E κ tT ⟶ rationalConfigurationGeometricScheme k κ sT)
    (hJT : JT.hom ≫ qT = WT.hom)
    (pT : (projectiveLineRatFuncModel κ).C ⟶ (projectiveLineRatFuncModel κ).C)
    (eT : RatFunc κ ≃ₐ[κ] RatFunc κ)
    (hplacesT : ∀ y : closedPoints (projectiveLineRatFuncModel κ).C,
      ∃ hy : pT.base y.val ∈ closedPoints (projectiveLineRatFuncModel κ).C,
        (projectiveLineRatFuncModel κ).placeOfPoint ⟨pT.base y.val, hy⟩ =
          ((projectiveLineRatFuncModel κ).placeOfPoint y).restrictAlong
            (ratFuncPairSquareHom eT) (ratFuncPairSquareHom_isIntegral eT))
    (hboundaryT : ∀ y : (projectiveLineRatFuncModel κ).C,
      y ∉ Set.range (rationalConfigurationBaseChangeChart E κ tT) ↔
        pT y ∉ Set.range (rationalConfigurationBaseChangeChart k κ sT))
    (hfieldT :
      let _hWIntegral : IsIntegral WT.left := isIntegral_left_of_isConnected_finiteEtale WT
      let _AKL : Algebra (rationalConfigurationGeometricScheme k κ sT).functionField
        WT.left.functionField :=
        finiteEtaleFunctionFieldAlgebra WT
      ∀ z : RatFunc κ,
        JT.hom.functionFieldMap JT.hom.homeomorph.surjective.denseRange
          (rationalConfigurationGeometricFunctionFieldEquiv E κ tT (ratFuncPairSquareHom eT z)) =
          algebraMap (rationalConfigurationGeometricScheme k κ sT).functionField
            WT.left.functionField
            (rationalConfigurationGeometricFunctionFieldEquiv k κ sT z))
 :
    let _hWIntegralS : IsIntegral WS.left := isIntegral_left_of_isConnected_finiteEtale WS
    let _AKLS : Algebra (rationalConfigurationGeometricScheme k κ sS).functionField
      WS.left.functionField :=
      finiteEtaleFunctionFieldAlgebra WS
    let liftS := fiberObjEquivHom ((rationalConfigurationGeometricScheme k κ
      sS).genericExtensionMorphism ΩS) WS wS
    let embS := finiteEtaleGenericHomFunctionFieldAlgHom WS liftS
    let eRS := JS.hom.functionFieldRingEquivOfIsOpenImmersion
    let _ANΩS : Algebra (rationalConfigurationGeometricScheme E κ tS).functionField ΩS :=
      (embS.toRingHom.comp eRS.toRingHom).toAlgebra
    let _hWIntegralT : IsIntegral WT.left := isIntegral_left_of_isConnected_finiteEtale WT
    let _AKLT : Algebra (rationalConfigurationGeometricScheme k κ sT).functionField
      WT.left.functionField :=
      finiteEtaleFunctionFieldAlgebra WT
    let liftT := fiberObjEquivHom ((rationalConfigurationGeometricScheme k κ
      sT).genericExtensionMorphism ΩT) WT wT
    let embT := finiteEtaleGenericHomFunctionFieldAlgHom WT liftT
    let eRT := JT.hom.functionFieldRingEquivOfIsOpenImmersion
    let _ANΩT : Algebra (rationalConfigurationGeometricScheme E κ tT).functionField ΩT :=
      (embT.toRingHom.comp eRT.toRingHom).toAlgebra
    ∃ hclosureS : IsAlgClosure (rationalConfigurationGeometricScheme E κ tS).functionField ΩS,
    let _modelClosureS : IsAlgClosure (rationalConfigurationGeometricScheme E κ tS).functionField
      ΩS := hclosureS
    ∃ hclosureT : IsAlgClosure (rationalConfigurationGeometricScheme E κ tT).functionField ΩT,
    let _modelClosureT : IsAlgClosure (rationalConfigurationGeometricScheme E κ tT).functionField
      ΩT := hclosureT
    ∃ hgeomS : (rationalConfigurationGeometricScheme E κ tS).genericExtensionMorphism ΩS ≫ qS =
      (rationalConfigurationGeometricScheme k κ sS).genericExtensionMorphism ΩS,
    ∃ hgeomT : (rationalConfigurationGeometricScheme E κ tT).genericExtensionMorphism ΩT ≫ qT =
      (rationalConfigurationGeometricScheme k κ sT).genericExtensionMorphism ΩT,
    ∀ (α : rationalConfigurationGeometricGroup k κ sS ΩS ≃ₜ*
          rationalConfigurationGeometricGroup k κ sT ΩT)
      (β : rationalConfigurationGeometricGroup E κ tS ΩS ≃ₜ*
          rationalConfigurationGeometricGroup E κ tT ΩT)
      (σ : sS ≃ sT) (τ : tS ≃ tT),
      (∀ z : sS, ∃ a : rationalConfigurationGeometricGroup k κ sT ΩT,
        (rationalConfigurationChosenInertia k κ sS ΩS (rationalConfigurationBoundaryPlace k κ sS
          z)).map
          α.toMonoidHom =
        (rationalConfigurationChosenInertia k κ sT ΩT (rationalConfigurationBoundaryPlace k κ sT
          (σ z))).map
          (MulAut.conj a).toMonoidHom) →
      (∀ z : tS, ∃ a : rationalConfigurationGeometricGroup E κ tT ΩT,
        (rationalConfigurationChosenInertia E κ tS ΩS (rationalConfigurationBoundaryPlace E κ tS
          z)).map
          β.toMonoidHom =
        (rationalConfigurationChosenInertia E κ tT ΩT (rationalConfigurationBoundaryPlace E κ tT
          (τ z))).map
          (MulAut.conj a).toMonoidHom) →
      (∀ x, pointedFundamentalGroupHom qT
          ((rationalConfigurationGeometricScheme E κ tT).genericExtensionMorphism ΩT)
          ((rationalConfigurationGeometricScheme k κ sT).genericExtensionMorphism ΩT) hgeomT (β x) =
        α (pointedFundamentalGroupHom qS
          ((rationalConfigurationGeometricScheme E κ tS).genericExtensionMorphism ΩS)
          ((rationalConfigurationGeometricScheme k κ sS).genericExtensionMorphism ΩS) hgeomS x)) →
      ∀ z : tS,
        σ (namedSquareGeometricOriginalLabelProjection k E κ sS tS pS eS hplacesS hboundaryS z) =
          namedSquareGeometricOriginalLabelProjection k E κ sT tT pT eT
            hplacesT hboundaryT (τ z) := by
  intro hWIntegralS AKLS liftS embS eRS ANΩS hWIntegralT AKLT liftT embT eRT ANΩT
  obtain ⟨hclosureS, hS⟩ := namedSquare_chosen_label_inertia_projection
    k E κ sS tS ΩS WS wS JS qS hJS pS eS hplacesS hboundaryS hfieldS
  let _modelClosureS :
      IsAlgClosure (rationalConfigurationGeometricScheme E κ tS).functionField ΩS := hclosureS
  change ∃ hgeomS : (rationalConfigurationGeometricScheme E κ tS).genericExtensionMorphism ΩS ≫ qS =
    (rationalConfigurationGeometricScheme k κ sS).genericExtensionMorphism ΩS, _ at hS
  obtain ⟨hgeomS, hprojS⟩ := hS
  obtain ⟨hclosureT, hT⟩ := namedSquare_chosen_label_inertia_projection
    k E κ sT tT ΩT WT wT JT qT hJT pT eT hplacesT hboundaryT hfieldT
  let _modelClosureT :
      IsAlgClosure (rationalConfigurationGeometricScheme E κ tT).functionField ΩT := hclosureT
  change ∃ hgeomT : (rationalConfigurationGeometricScheme E κ tT).genericExtensionMorphism ΩT ≫ qT =
    (rationalConfigurationGeometricScheme k κ sT).genericExtensionMorphism ΩT, _ at hT
  obtain ⟨hgeomT, hprojT⟩ := hT
  refine ⟨hclosureS, ?_⟩
  intro suppliedClosureS
  refine ⟨hclosureT, ?_⟩
  intro suppliedClosureT
  refine ⟨hgeomS, hgeomT, ?_⟩
  intro α β σ τ hbase hcover hsquare
  let iS := (pointedFundamentalGroupHom qS
    ((rationalConfigurationGeometricScheme E κ tS).genericExtensionMorphism ΩS)
    ((rationalConfigurationGeometricScheme k κ sS).genericExtensionMorphism ΩS) hgeomS).toMonoidHom
  let iT := (pointedFundamentalGroupHom qT
    ((rationalConfigurationGeometricScheme E κ tT).genericExtensionMorphism ΩT)
    ((rationalConfigurationGeometricScheme k κ sT).genericExtensionMorphism ΩT) hgeomT).toMonoidHom
  have hiS : Function.Injective iS :=
    namedSquare_induced_model_projection_injective ΩS WS wS JS qS hJS hgeomS
  apply punctureProjection_commutes_of_inertia_inclusion_square
    α.toMulEquiv β.toMulEquiv iS iT hiS hsquare
    (fun z : sS => rationalConfigurationChosenInertia k κ sS ΩS
      (rationalConfigurationBoundaryPlace k κ sS z))
    (fun z : sT => rationalConfigurationChosenInertia k κ sT ΩT
      (rationalConfigurationBoundaryPlace k κ sT z))
    (fun z : tS => rationalConfigurationChosenInertia E κ tS ΩS
      (rationalConfigurationBoundaryPlace E κ tS z))
    (fun z : tT => rationalConfigurationChosenInertia E κ tT ΩT
      (rationalConfigurationBoundaryPlace E κ tT z))
    σ τ
    (namedSquareGeometricOriginalLabelProjection k E κ sS tS pS eS hplacesS hboundaryS)
    (namedSquareGeometricOriginalLabelProjection k E κ sT tT pT eT hplacesT hboundaryT)
    hbase hcover hprojS hprojT
  · intro z
    exact rationalConfigurationChosenInertia_exists_ne_one E κ tS htS ΩS
      (rationalConfigurationBoundaryPlace E κ tS z)
  · intro p q a b x hx hp hq
    apply (rationalConfigurationBoundaryPlaceEquiv k κ sT).injective
    exact rationalConfigurationChosenInertia_common_ne_one_imp_eq k κ sT hsT ΩT
      (rationalConfigurationBoundaryPlace k κ sT p) (rationalConfigurationBoundaryPlace k κ sT q)
      a b x hx hp hq

end AnabelianGeometry.WeightFiltration
