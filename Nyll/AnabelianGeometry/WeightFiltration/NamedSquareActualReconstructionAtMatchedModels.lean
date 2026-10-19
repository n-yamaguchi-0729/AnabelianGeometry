/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareActualReconstruction
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareLiteralPointModel

/-! # Reconstruction at the matched geometric models -/

noncomputable section
open scoped RatFunc
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups EtaleFundamentalGroups.Inertia
open CategoryTheory.PreGaloisCategory AnabelianGeometry.KummerTheory
open AnabelianGeometry.ProjectiveLine
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra Classical.propDecidable
namespace AnabelianGeometry.WeightFiltration

theorem namedSquare_actual_matched_models_reconstruct_same_punctures
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
    (AS : Algebra (rationalConfigurationGeometricScheme E κ tS).functionField ΩS)
    (AT : Algebra (rationalConfigurationGeometricScheme E κ tT).functionField ΩT)
    (hmodelS : let _A : Algebra (rationalConfigurationGeometricScheme E κ tS).functionField ΩS := AS
      (rationalConfigurationGeometricScheme E κ tS).genericExtensionMorphism ΩS =
        actualFiberPointLift
          ((rationalConfigurationGeometricScheme k κ sS).genericExtensionMorphism ΩS) WS wS ≫
            JS.hom)
    (hmodelT : let _A : Algebra (rationalConfigurationGeometricScheme E κ tT).functionField ΩT := AT
      (rationalConfigurationGeometricScheme E κ tT).genericExtensionMorphism ΩT =
        actualFiberPointLift
          ((rationalConfigurationGeometricScheme k κ sT).genericExtensionMorphism ΩT) WT wT ≫
            JT.hom)
 :
    let _hWIntegralS : IsIntegral WS.left := isIntegral_left_of_isConnected_finiteEtale WS
    let _AKLS : Algebra (rationalConfigurationGeometricScheme k κ sS).functionField
      WS.left.functionField :=
      finiteEtaleFunctionFieldAlgebra WS
    let liftS := fiberObjEquivHom ((rationalConfigurationGeometricScheme k κ
      sS).genericExtensionMorphism ΩS) WS wS
    let _embS := finiteEtaleGenericHomFunctionFieldAlgHom WS liftS
    let _eRS := JS.hom.functionFieldRingEquivOfIsOpenImmersion
    let _ANΩS : Algebra (rationalConfigurationGeometricScheme E κ tS).functionField ΩS :=
      AS
    let _hWIntegralT : IsIntegral WT.left := isIntegral_left_of_isConnected_finiteEtale WT
    let _AKLT : Algebra (rationalConfigurationGeometricScheme k κ sT).functionField
      WT.left.functionField :=
      finiteEtaleFunctionFieldAlgebra WT
    let liftT := fiberObjEquivHom ((rationalConfigurationGeometricScheme k κ
      sT).genericExtensionMorphism ΩT) WT wT
    let _embT := finiteEtaleGenericHomFunctionFieldAlgHom WT liftT
    let _eRT := JT.hom.functionFieldRingEquivOfIsOpenImmersion
    let _ANΩT : Algebra (rationalConfigurationGeometricScheme E κ tT).functionField ΩT :=
      AT
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
  have hAS := namedModelAmbientAlgebra_eq_of_genericPoint WS wS JS AS hmodelS
  have hAT := namedModelAmbientAlgebra_eq_of_genericPoint WT wT JT AT hmodelT
  dsimp only at hAS hAT
  subst AS
  subst AT
  exact namedSquare_actual_models_reconstruct_same_punctures
    k E κ sS sT tS tT hsT htS htT
    ΩS WS wS JS qS hJS pS eS hplacesS hboundaryS hfieldS
    ΩT WT wT JT qT hJT pT eT hplacesT hboundaryT hfieldT
    pSE eSE hcoeffS hplacesSE hlabelsS pTE eTE hcoeffT hplacesTE hlabelsT

end AnabelianGeometry.WeightFiltration
