/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareRecoveredLabelCommutation
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareLabelProjectionBaseChange
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareArithmeticReconstruction
import Nyll.AnabelianGeometry.WeightFiltration.FixedGeometricLiftedCyclicClasses

/-! # Reconstruction from actual named square models -/

noncomputable section
open scoped RatFunc
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups EtaleFundamentalGroups.Inertia
open CategoryTheory.PreGaloisCategory AnabelianGeometry.KummerTheory
open AnabelianGeometry.ProjectiveLine
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra Classical.propDecidable
namespace AnabelianGeometry.WeightFiltration

theorem namedSquare_actual_models_reconstruct_same_punctures
    (k E κ : Type) [Field k] [NumberField k] [Field E] [NumberField E]
    [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k κ] [Algebra E κ] [Algebra k E] [IsScalarTower k E κ]
    [IsAlgClosure k κ] [IsAlgClosure E κ]
    [Algebra.IsAlgebraic k E] [Algebra.IsSeparable k E]
    (sS sT : Finset (Projectivization k (k × k)))
    (tS tT : Finset (Projectivization E (E × E)))
    (hsT : 3 ≤ sT.card) (htS : 3 ≤ tS.card) (htT : 3 ≤ tT.card)
    [IsNormalIntegral (rationalConfigurationGeometricScheme k κ sS)]
    [IsLocallyNoetherian (rationalConfigurationGeometricScheme k κ sS)]
    [ConnectedSpace (rationalConfigurationGeometricScheme k κ sS)]
    (ΩS : Type) [Field ΩS] [IsAlgClosed ΩS] [IsSepClosed ΩS]
    [Algebra (rationalConfigurationGeometricScheme k κ sS).functionField ΩS]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ sS).functionField ΩS]
    (WS : FiniteEtale (rationalConfigurationGeometricScheme k κ sS))
      [CategoryTheory.PreGaloisCategory.IsConnected WS]
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
    (WT : FiniteEtale (rationalConfigurationGeometricScheme k κ sT))
      [CategoryTheory.PreGaloisCategory.IsConnected WT]
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
    (pSE : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
    (eSE : RatFunc E ≃ₐ[E] RatFunc E)
    (hcoeffS : pS ≫ map E κ 1 = map E κ 1 ≫ pSE)
    (hplacesSE : ∀ y : closedPoints (projectiveLineRatFuncModel E).C,
      ∃ hy : pSE.base y.val ∈ closedPoints (projectiveLineRatFuncModel E).C,
        (projectiveLineRatFuncModel E).placeOfPoint ⟨pSE.base y.val, hy⟩ =
          ((projectiveLineRatFuncModel E).placeOfPoint y).restrictAlong
            (ratFuncPairSquareHom eSE) (ratFuncPairSquareHom_isIntegral eSE))
    (hlabelsS : ∀ z, z ∈ tS ↔ projectiveRationalPoint z ∉ Set.range
      (Limits.pullback.fst pSE (rationalConfigurationBaseChangeChart k E sS)))
    (pTE : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
    (eTE : RatFunc E ≃ₐ[E] RatFunc E)
    (hcoeffT : pT ≫ map E κ 1 = map E κ 1 ≫ pTE)
    (hplacesTE : ∀ y : closedPoints (projectiveLineRatFuncModel E).C,
      ∃ hy : pTE.base y.val ∈ closedPoints (projectiveLineRatFuncModel E).C,
        (projectiveLineRatFuncModel E).placeOfPoint ⟨pTE.base y.val, hy⟩ =
          ((projectiveLineRatFuncModel E).placeOfPoint y).restrictAlong
            (ratFuncPairSquareHom eTE) (ratFuncPairSquareHom_isIntegral eTE))
    (hlabelsT : ∀ z, z ∈ tT ↔ projectiveRationalPoint z ∉ Set.range
      (Limits.pullback.fst pTE (rationalConfigurationBaseChangeChart k E sT)))
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
      (βP : rationalConfigurationArithmeticGroup E κ tS ΩS ≃ₜ*
        rationalConfigurationArithmeticGroup E κ tT ΩT)
      (_hβP : ∀ z,
        arithmeticFundamentalGroupHom E κ ((rationalConfigurationOpen tT).ι ≫ π E 1)
          (rationalConfigurationArithmeticBasePoint E κ tT ΩT) (βP z) =
        arithmeticFundamentalGroupHom E κ ((rationalConfigurationOpen tS).ι ≫ π E 1)
          (rationalConfigurationArithmeticBasePoint E κ tS ΩS) z)
      (β : rationalConfigurationGeometricGroup E κ tS ΩS ≃ₜ*
          rationalConfigurationGeometricGroup E κ tT ΩT)
      (_hβ : ∀ z, rationalConfigurationGeometricInclusion E κ tT ΩT (β z) =
        βP (rationalConfigurationGeometricInclusion E κ tS ΩS z))
      (σ : sS ≃ sT),
      (∀ z : sS, ∃ a : rationalConfigurationGeometricGroup k κ sT ΩT,
        (rationalConfigurationChosenInertia k κ sS ΩS
          (rationalConfigurationBoundaryPlace k κ sS z)).map α.toMonoidHom =
        (rationalConfigurationChosenInertia k κ sT ΩT
          (rationalConfigurationBoundaryPlace k κ sT (σ z))).map (MulAut.conj a).toMonoidHom) →
      (∀ x, pointedFundamentalGroupHom qT
          ((rationalConfigurationGeometricScheme E κ tT).genericExtensionMorphism ΩT)
          ((rationalConfigurationGeometricScheme k κ sT).genericExtensionMorphism ΩT) hgeomT (β x) =
        α (pointedFundamentalGroupHom qS
          ((rationalConfigurationGeometricScheme E κ tS).genericExtensionMorphism ΩS)
          ((rationalConfigurationGeometricScheme k κ sS).genericExtensionMorphism ΩS) hgeomS x)) →
      (∀ (a b c₀ c : sS), a ≠ b → c₀ ≠ a → c₀ ≠ b → c ≠ a → c ≠ b →
        ∃ A B : kˣ,
          (A : k) = crossRatio a.val b.val c₀.val c.val ∧
          (B : k) = crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val ∧
          Subgroup.zpowers A = Subgroup.zpowers B) →
      ∀ (a b c₀ : sS) (hab : a ≠ b) (h₀a : c₀ ≠ a) (h₀b : c₀ ≠ b)
        (VS₀ VSinf VT₀ VTinf : Place k (RatFunc k))
        (f g : RatFunc k) (_hf : f ≠ 0) (_hg : g ≠ 0)
        (_hfS : eSE RatFunc.X = algebraMap (RatFunc k) (RatFunc E) f)
        (_hfT : eTE RatFunc.X = algebraMap (RatFunc k) (RatFunc E) g)
        (_harithS : ∀ V : Place k (RatFunc k), V.ord f =
          (if V = VS₀ then 1 else 0) - (if V = VSinf then 1 else 0))
        (_harithT : ∀ V : Place k (RatFunc k), V.ord g =
          (if V = VT₀ then 1 else 0) - (if V = VTinf then 1 else 0))
        (_hgeomf : ∀ V : Place κ (RatFunc κ),
          V.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
            (if V = (rationalConfigurationBoundaryPlace k κ sS a).val then 1 else 0) -
            (if V = (rationalConfigurationBoundaryPlace k κ sS b).val then 1 else 0))
        (_hgeomg : ∀ V : Place κ (RatFunc κ),
          V.ord (algebraMap (RatFunc k) (RatFunc κ) g) =
            (if V = (rationalConfigurationBoundaryPlace k κ sT (σ a)).val then 1 else 0) -
            (if V = (rationalConfigurationBoundaryPlace k κ sT (σ b)).val then 1 else 0))
        (rS : sS → E) (rT : sT → E)
        (_hrS : ∀ x : sS, rS x ^ 2 = algebraMap k E
          ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt f))
        (_hrT : ∀ x : sT, rT x ^ 2 = algebraMap k E
          ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt g)),
      ∃ τ : tS ≃ tT,
        (∀ z : tS, ∃ d : rationalConfigurationGeometricGroup E κ tT ΩT,
          (rationalConfigurationChosenInertia E κ tS ΩS
            (rationalConfigurationBoundaryPlace E κ tS z)).map β.toMonoidHom =
          (rationalConfigurationChosenInertia E κ tT ΩT
            (rationalConfigurationBoundaryPlace E κ tT (τ z))).map
              (MulAut.conj d).toMonoidHom) ∧
        (∀ z : tS,
          namedSquareOriginalLabelProjection k E sT pTE eTE hplacesTE tT hlabelsT (τ z) =
            σ (namedSquareOriginalLabelProjection k E sS pSE eSE hplacesSE tS hlabelsS z)) ∧
        ∀ c : sS,
          matchTriples a.val b.val c₀.val (σ a).val (σ b).val (σ c₀).val
            (fun h => hab (Subtype.ext h)) (fun h => h₀b (Subtype.ext h))
            (fun h => h₀a (Subtype.ext h))
            (fun h => hab (σ.injective (Subtype.ext h)))
            (fun h => h₀b (σ.injective (Subtype.ext h)))
            (fun h => h₀a (σ.injective (Subtype.ext h))) c.val = (σ c).val := by
  intro hWIntegralS AKLS liftS embS eRS ANΩS hWIntegralT AKLT liftT embT eRT ANΩT
  obtain ⟨hclosureS, hrestS⟩ := namedSquare_recovered_label_projection_commutes
    k E κ sS sT tS tT hsT htS ΩS WS wS JS qS hJS pS eS hplacesS hboundaryS hfieldS
      ΩT WT wT JT qT hJT pT eT hplacesT hboundaryT hfieldT
  let _modelClosureS := hclosureS
  obtain ⟨hclosureT, hrestT⟩ := hrestS
  let _modelClosureT := hclosureT
  obtain ⟨hgeomS, hgeomT, hrecovered⟩ := hrestT
  refine ⟨hclosureS, ?_⟩
  intro suppliedClosureS
  refine ⟨hclosureT, ?_⟩
  intro suppliedClosureT
  refine ⟨hgeomS, hgeomT, ?_⟩
  intro α βP _hβP β _hβ σ hIσ hsquare hbase a b c₀ hab h₀a h₀b
    VS₀ VSinf VT₀ VTinf f g _hf _hg _hfS _hfT _harithS _harithT _hgeomf _hgeomg rS rT _hrS _hrT
  obtain ⟨τ, hIτ, hlift⟩ := bare_rationalConfiguration_crossRatio_cyclic_classes_fixed_geometric
    E κ tS tT htS htT ΩS ΩT βP _hβP β _hβ
  have hcommκ := hrecovered α β σ τ hIσ hIτ hsquare
  have hprojS := namedSquareGeometricOriginalLabelProjection_eq_original
    k E κ sS tS pSE pS hcoeffS eSE eS hplacesSE hplacesS hlabelsS hboundaryS
  have hprojT := namedSquareGeometricOriginalLabelProjection_eq_original
    k E κ sT tT pTE pT hcoeffT eTE eT hplacesTE hplacesT hlabelsT hboundaryT
  have hcomm : ∀ z : tS,
      namedSquareOriginalLabelProjection k E sT pTE eTE hplacesTE tT hlabelsT (τ z) =
        σ (namedSquareOriginalLabelProjection k E sS pSE eSE hplacesSE tS hlabelsS z) := by
    intro z
    exact (hprojT (τ z)).symm.trans ((hcommκ z).symm.trans (congrArg σ (hprojS z)))
  refine ⟨τ, hIτ, hcomm, ?_⟩
  let fS := algebraMap (RatFunc k) (RatFunc E) f
  let fT := algebraMap (RatFunc k) (RatFunc E) g
  let vS : sS → E := fun x => (rationalConfigurationBoundaryPlace k E sS x).val.evalAt fS
  let vT : sT → E := fun x => (rationalConfigurationBoundaryPlace k E sT x).val.evalAt fT
  obtain ⟨hzS, hpS, hvS, hratioS⟩ := namedSquare_original_pair_values_over_extension
    k κ E sS a b c₀ hab h₀b VS₀ VSinf f _hf _harithS _hgeomf
  obtain ⟨hzT, hpT, hvT, hratioT⟩ := namedSquare_original_pair_values_over_extension
    k κ E sT (σ a) (σ b) (σ c₀) (σ.injective.ne hab) (σ.injective.ne h₀b)
      VT₀ VTinf g _hg _harithT _hgeomg
  have hrootS := rationalConfigurationBoundaryPlace_coefficient_square_values k E sS f _hf rS _hrS
  have hrootT := rationalConfigurationBoundaryPlace_coefficient_square_values k E sT g _hg rT _hrT
  exact namedSquareModels_match_configuration
    k E sS sT tS tT pSE eSE hplacesSE hlabelsS pTE eTE hplacesTE hlabelsT
    σ τ hcomm hbase hlift a b c₀ hab h₀a h₀b fS fT _hfS _hfT vS rS vT rT
    (fun x _ => hrootS x) (fun x _ => hrootT x)
    hzS hzT hpS hpT hvS hvT hratioS
    (fun c hcb => hratioT (σ c) (σ.injective.ne hcb))

end AnabelianGeometry.WeightFiltration
