/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalPointedSquareData
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticBoundaryFiniteLabels
import Nyll.AnabelianGeometry.WeightFiltration.RationalConfigurationMatchedGenericAmbient
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareFiniteBaseFiberTransport
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareCorrectedGeometricComparison
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareLiteralBaseTransport
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareLiteralGeometricMap
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareLiteralPointModel
import Nyll.EtaleFundamentalGroups.GaloisCategories.CoverTransportFiber
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticConstantFieldCoverGroupTransport
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
import Nyll.EtaleFundamentalGroups.GeometricFiber.ConstantFieldInclusionFiberPoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.RecoveredCoverGenericPoint
import Nyll.ProCGroups.Topologies.ArithmeticInnerCorrectionFiberTransport
import Nyll.SchemeTheory.BaseChange.BaseChangedIdentifiedModelIso
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineGeometry
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareMatchedPointModel
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareActualPointedGeometricSquare
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquarePointedLiteralGeometricMap
import Nyll.AnabelianGeometry.WeightFiltration.CorrectedMatchedAmbientPunctures
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareActualReconstructionAtMatchedModels
import Nyll.AnabelianGeometry.WeightFiltration.RationalConfigurationMatchIso
import Mathlib.Data.Fintype.EquivFin

/-!
# Reconstruction of rational configurations from arithmetic fundamental groups
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace EtaleFundamentalGroups
open AnabelianGeometry.ProjectiveLine CategoryTheory.PreGaloisCategory
open AnabelianGeometry.KummerTheory
open scoped FintypeCatDiscrete RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra Classical.propDecidable
  CurveModel.isIntegral
namespace AnabelianGeometry.WeightFiltration

local instance nakamuraOverCategory (S : Scheme) :
    Category (MorphismProperty.Over (@IsFiniteEtale : MorphismProperty Scheme) ⊤ S) :=
  AlgebraicGeometry.FiniteEtale.instCategory S
local instance nakamuraHasPullbacksAlong {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun _ _ ↦ inferInstance⟩
local instance nakamuraStableUnderBaseChangeAlong {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme)) h hf⟩

attribute [local instance] pointedSquareChart_isOpenImmersion literalPoint_projectiveIntegral

private theorem nakamura_reconstruct_literal_models
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
            JT.hom) :
    let _modelAS : Algebra (rationalConfigurationGeometricScheme E κ tS).functionField ΩS := AS
    let _modelAT : Algebra (rationalConfigurationGeometricScheme E κ tT).functionField ΩT := AT
    ∀ (hgeomS : (rationalConfigurationGeometricScheme E κ tS).genericExtensionMorphism ΩS ≫ qS =
        (rationalConfigurationGeometricScheme k κ sS).genericExtensionMorphism ΩS)
      (hgeomT : (rationalConfigurationGeometricScheme E κ tT).genericExtensionMorphism ΩT ≫ qT =
        (rationalConfigurationGeometricScheme k κ sT).genericExtensionMorphism ΩT),
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
      ∀ (a b c₀ : sS) (_hab : a ≠ b) (_h₀a : c₀ ≠ a) (_h₀b : c₀ ≠ b)
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
      ∃ F : (k × k) ≃ₗ[k] (k × k),
        (∀ p : sS, projectiveLinearEquiv F p.val = (σ p).val) ∧
        ∃ I : (rationalConfigurationOpen sS : Scheme) ≅ (rationalConfigurationOpen sT : Scheme),
          I.hom ≫ (rationalConfigurationOpen sT).ι =
            (rationalConfigurationOpen sS).ι ≫ (pairLinearCoordinateIso F).hom ∧
          I.hom ≫ ((rationalConfigurationOpen sT).ι ≫ π k 1) =
            (rationalConfigurationOpen sS).ι ≫ π k 1 := by
  intro modelAS modelAT hgeomS hgeomT α βP hβP β hβ σ hIL hsquare hclasses
    a b c₀ hab h₀a h₀b VS₀ VSinf VT₀ VTinf f g hf hg heSE heTE harithS harithT
    hgeomf hgeomg rS rT hrS hrT
  obtain ⟨hclosureMS, hclosureMT, _hprojMS, _hprojMT, Hnumeric⟩ :=
    namedSquare_actual_matched_models_reconstruct_same_punctures
      k E κ sS sT tS tT hsT htS htT
      ΩS WS wS JS qS hJS pS eS hplacesS hboundaryS hfieldS
      ΩT WT wT JT qT hJT pT eT hplacesT hboundaryT hfieldT
      pSE eSE hcoeffS hplacesSE hlabelsS pTE eTE hcoeffT hplacesTE hlabelsT
      AS AT hmodelS hmodelT
  let : IsAlgClosure (rationalConfigurationGeometricScheme E κ tS).functionField ΩS := hclosureMS
  let : IsAlgClosure (rationalConfigurationGeometricScheme E κ tT).functionField ΩT := hclosureMT
  obtain ⟨τ, _hIτ, _hcomm, hmatch⟩ := Hnumeric α βP hβP β hβ σ hIL hsquare
    hclasses a b c₀ hab h₀a h₀b VS₀ VSinf VT₀ VTinf
    f g hf hg heSE heTE harithS harithT hgeomf hgeomg rS rT hrS hrT
  obtain ⟨hlinear, I, hambient, hover⟩ := rationalConfiguration_schemeIso_of_matchTriples
    k sS sT σ a b c₀ hab h₀a h₀b hmatch
  exact ⟨_, hlinear, I, hambient, hover⟩

private theorem nakamura_finish_named_models
    (k E κ : Type) [Field k] [NumberField k] [Field E] [NumberField E]
    [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k κ] [Algebra k E] [Algebra E κ] [IsScalarTower k E κ]
    [IsAlgClosure k κ] [IsAlgClosure E κ]
    [Algebra.IsAlgebraic k E] [Algebra.IsSeparable k E] [IsSepClosure E κ]
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
    (s t : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [AoldS : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [AoldT : Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    [HoldS : IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [HoldT : IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (eP : rationalConfigurationArithmeticGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ω₂)
    (hP : ∀ γ,
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ t Ω₂) (eP γ) =
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ s Ω₁) γ)
    (eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationGeometricGroup k κ t Ω₂)
    (hΔ : ∀ v, rationalConfigurationGeometricInclusion k κ t Ω₂ (eΔ v) =
      eP (rationalConfigurationGeometricInclusion k κ s Ω₁ v))
    (σ : s ≃ t)
    (hI : ∀ p : s, ∃ a : rationalConfigurationGeometricGroup k κ t Ω₂,
      (rationalConfigurationChosenInertia k κ s Ω₁
        (rationalConfigurationBoundaryPlace k κ s p)).map eΔ.toMonoidHom =
      (rationalConfigurationChosenInertia k κ t Ω₂
        (rationalConfigurationBoundaryPlace k κ t (σ p))).map (MulAut.conj a).toMonoidHom)
    (hclasses : ∀ (a b c₀ c : s), a ≠ b → c₀ ≠ a → c₀ ≠ b → c ≠ a → c ≠ b →
      ∃ A B : kˣ,
        (A : k) = crossRatio a.val b.val c₀.val c.val ∧
        (B : k) = crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val ∧
        Subgroup.zpowers A = Subgroup.zpowers B)
    (a b c₀ : s) (hab : a ≠ b) (h₀a : c₀ ≠ a) (h₀b : c₀ ≠ b)
    (VS₀ VSinf VT₀ VTinf : Place k (RatFunc k))
    (f g : RatFunc k) (hf : f ≠ 0) (hg : g ≠ 0)
    (harithS : ∀ V : Place k (RatFunc k), V.ord f =
      (if V = VS₀ then 1 else 0) - (if V = VSinf then 1 else 0))
    (harithT : ∀ V : Place k (RatFunc k), V.ord g =
      (if V = VT₀ then 1 else 0) - (if V = VTinf then 1 else 0))
    (hgeomf : ∀ V : Place κ (RatFunc κ), V.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
      (if V = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
      (if V = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0))
    (hgeomg : ∀ V : Place κ (RatFunc κ), V.ord (algebraMap (RatFunc k) (RatFunc κ) g) =
      (if V = (rationalConfigurationBoundaryPlace k κ t (σ a)).val then 1 else 0) -
      (if V = (rationalConfigurationBoundaryPlace k κ t (σ b)).val then 1 else 0))
    (rS : s → E) (rT : t → E)
    (hrS : ∀ x : s, rS x ^ 2 = algebraMap k E
      ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt f))
    (hrT : ∀ x : t, rT x ^ 2 = algebraMap k E
      ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt g)) :
    let fs := (rationalConfigurationOpen s).ι ≫ π k 1
    let ft := (rationalConfigurationOpen t).ι ≫ π k 1
    let xs := rationalConfigurationArithmeticBasePoint k κ s Ω₁
    let xt := rationalConfigurationArithmeticBasePoint k κ t Ω₂
    let ys := arithmeticConstantFieldLift k E κ fs xs
    let yt := arithmeticConstantFieldLift k E κ ft xt
    let _bs := ((FiniteEtale.pullback fs).obj (originalConstantFieldCover k E)).hom
    let _bt := ((FiniteEtale.pullback ft).obj (originalConstantFieldCover k E)).hom
    let _hs0 := arithmeticConstantFieldLift_comp k E κ fs xs
    let _ht0 := arithmeticConstantFieldLift_comp k E κ ft xt
    let cs := Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) fs
    let ct := Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) ft
    let φ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
    let bκS := Limits.pullback.snd φ cs
    let bκT := Limits.pullback.snd φ ct
    let GS := Limits.pullback φ cs
    let GT := Limits.pullback φ ct
    let _hGS : IsIntegral GS := rationalConfiguration_coefficientTower_isIntegral k E κ s
    let _hGT : IsIntegral GT := rationalConfiguration_coefficientTower_isIntegral k E κ t
    let _hNS : IsNormalIntegral GS := namedSquareMatchedBase_isNormalIntegral k E κ s
    let _hNT : IsNormalIntegral GT := namedSquareMatchedBase_isNormalIntegral k E κ t
    let _hLS : IsLocallyNoetherian GS := namedSquareMatchedBase_isLocallyNoetherian k E κ s
    let _hLT : IsLocallyNoetherian GT := namedSquareMatchedBase_isLocallyNoetherian k E κ t
    ∀ (aS : GS.functionField →+* Ω₁) (aT : GT.functionField →+* Ω₂),
    let _AS : Algebra GS.functionField Ω₁ := aS.toAlgebra
    let _AT : Algebra GT.functionField Ω₂ := aT.toAlgebra
    ∀ (hclosureS : IsAlgClosure GS.functionField Ω₁)
      (hclosureT : IsAlgClosure GT.functionField Ω₂),
    let _ := hclosureS
    let _ := hclosureT
    let ξS := GS.genericExtensionMorphism Ω₁
    let ξT := GT.genericExtensionMorphism Ω₂
    ∀ (hpointS : ξS ≫ bκS = ys) (hpointT : ξT ≫ bκT = yt) (c : π₁ᵉᵗ(yt)),
    let αE := arithmeticConstantFieldCoverGroupTransport k E κ fs ft xs xt eP hP
    let αc := ProCGroups.innerCorrectedGroupEquiv αE c
    ∀ (_hstrict : ∀ z, arithmeticFundamentalGroupHom E κ ct yt (αc z) =
        arithmeticFundamentalGroupHom E κ cs ys z)
      (WES : FiniteEtale (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) fs))
      (WET : FiniteEtale (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) ft))
      (hconnES : CategoryTheory.PreGaloisCategory.IsConnected WES)
      (hconnET : CategoryTheory.PreGaloisCategory.IsConnected WET),
    let _ := hconnES
    let _ := hconnET
    ∀ (ec : (fiber ys).obj WES ≃ (fiber yt).obj WET)
      (_hfiber : fiberEquivariant ys yt WES WET αc ec) (wE : (fiber ys).obj WES),
    let wET := ec wE
    let WS := (FiniteEtale.pullback bκS).obj WES
    let WT := (FiniteEtale.pullback bκT).obj WET
    ∀ (hconnS : CategoryTheory.PreGaloisCategory.IsConnected WS)
      (hconnT : CategoryTheory.PreGaloisCategory.IsConnected WT),
    let _ := hconnS
    let _ := hconnT
    let wS := (pointedPullbackFiberEquiv bκS ξS ys hpointS WES).symm wE
    let wT := (pointedPullbackFiberEquiv bκT ξT yt hpointT WET).symm wET
    ∀ (tS tT : Finset (Projectivization E (E × E)))
      (JS : WES.left ≅ (rationalConfigurationOpen tS : Scheme))
      (JT : WET.left ≅ (rationalConfigurationOpen tT : Scheme))
      (qES : (rationalConfigurationOpen tS : Scheme) ⟶ Limits.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k E))) fs)
      (qET : (rationalConfigurationOpen tT : Scheme) ⟶ Limits.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k E))) ft)
      (_hJS : JS.hom ≫ qES = WES.hom) (_hJT : JT.hom ≫ qET = WET.hom)
      (_hstructS : qES ≫ cs = (rationalConfigurationOpen tS).ι ≫ π E 1)
      (_hstructT : qET ≫ ct = (rationalConfigurationOpen tT).ι ≫ π E 1)
      (JκS : WS.left ≅ rationalConfigurationGeometricScheme E κ tS)
      (JκT : WT.left ≅ rationalConfigurationGeometricScheme E κ tT)
      (eS eT : RatFunc κ ≃ₐ[κ] RatFunc κ)
      (pS pT : (projectiveLineRatFuncModel κ).C ⟶ (projectiveLineRatFuncModel κ).C)
      (hjκS : IsOpenImmersion (namedSquareConstantProjectionChart k E κ s))
      (hjκT : IsOpenImmersion (namedSquareConstantProjectionChart k E κ t)),
    let _ := hjκS
    let _ := hjκT
    ∀ (_hboundaryS : ∀ z : (projectiveLineRatFuncModel κ).C,
        z ∉ Set.range (rationalConfigurationBaseChangeChart E κ tS) ↔
          pS z ∉ Set.range (namedSquareConstantProjectionChart k E κ s))
      (_hboundaryT : ∀ z : (projectiveLineRatFuncModel κ).C,
        z ∉ Set.range (rationalConfigurationBaseChangeChart E κ tT) ↔
          pT z ∉ Set.range (namedSquareConstantProjectionChart k E κ t))
      (_hcardS : Nat.card ((projectiveLineRatFuncModel κ).openBoundaryPlaces
        (namedSquareConstantProjectionChart k E κ s)) ≤ tS.card)
      (_hcardT : Nat.card ((projectiveLineRatFuncModel κ).openBoundaryPlaces
        (namedSquareConstantProjectionChart k E κ t)) ≤ tT.card)
      (_hfieldS :
        let _hW : IsIntegral WS.left := isIntegral_left_of_isConnected_finiteEtale WS
        let _AW : Algebra GS.functionField WS.left.functionField :=
          finiteEtaleFunctionFieldAlgebra WS
        ∀ z : RatFunc κ,
          JκS.hom.functionFieldMap JκS.hom.homeomorph.surjective.denseRange
            (rationalConfigurationGeometricFunctionFieldEquiv E κ tS (ratFuncPairSquareHom eS z)) =
          algebraMap GS.functionField WS.left.functionField
            (((projectiveLineRatFuncModel κ).ffEquiv.trans
              (namedSquareConstantProjectionChart k E κ
                s).functionFieldRingEquivOfIsOpenImmersion) z))
      (_hfieldT :
        let _hW : IsIntegral WT.left := isIntegral_left_of_isConnected_finiteEtale WT
        let _AW : Algebra GT.functionField WT.left.functionField :=
          finiteEtaleFunctionFieldAlgebra WT
        ∀ z : RatFunc κ,
          JκT.hom.functionFieldMap JκT.hom.homeomorph.surjective.denseRange
            (rationalConfigurationGeometricFunctionFieldEquiv E κ tT (ratFuncPairSquareHom eT z)) =
          algebraMap GT.functionField WT.left.functionField
            (((projectiveLineRatFuncModel κ).ffEquiv.trans
              (namedSquareConstantProjectionChart k E κ
                t).functionFieldRingEquivOfIsOpenImmersion) z))
      (AMS : Algebra (rationalConfigurationGeometricScheme E κ tS).functionField Ω₁)
      (AMT : Algebra (rationalConfigurationGeometricScheme E κ tT).functionField Ω₂),
    let _ := AMS
    let _ := AMT
    let qκS := JκS.inv ≫ WS.hom
    let qκT := JκT.inv ≫ WT.hom
    ∀ (_hmodelS : (rationalConfigurationGeometricScheme E κ tS).genericExtensionMorphism Ω₁ =
        actualFiberPointLift ξS WS wS ≫ JκS.hom)
      (_hmodelT : (rationalConfigurationGeometricScheme E κ tT).genericExtensionMorphism Ω₂ =
        actualFiberPointLift ξT WT wT ≫ JκT.hom)
      (_hgeomS : (rationalConfigurationGeometricScheme E κ tS).genericExtensionMorphism Ω₁ ≫
        qκS = ξS)
      (_hgeomT : (rationalConfigurationGeometricScheme E κ tT).genericExtensionMorphism Ω₂ ≫
        qκT = ξT)
      (_hmodelarithS : rationalConfigurationArithmeticBasePoint E κ tS Ω₁ =
        namedModelPoint WES ys wE JS)
      (_hmodelarithT : rationalConfigurationArithmeticBasePoint E κ tT Ω₂ =
        namedModelPoint WET yt wET JT)
      (_hqκcoeffS : qκS ≫ bκS = Limits.pullback.snd φ
        ((rationalConfigurationOpen tS).ι ≫ π E 1) ≫ qES)
      (_hqκcoeffT : qκT ≫ bκT = Limits.pullback.snd φ
        ((rationalConfigurationOpen tT).ι ≫ π E 1) ≫ qET)
      (_hplacesS : ∀ y : closedPoints (projectiveLineRatFuncModel κ).C,
        ∃ hy : pS.base y.val ∈ closedPoints (projectiveLineRatFuncModel κ).C,
          (projectiveLineRatFuncModel κ).placeOfPoint ⟨pS.base y.val, hy⟩ =
            ((projectiveLineRatFuncModel κ).placeOfPoint y).restrictAlong
              (ratFuncPairSquareHom eS) (ratFuncPairSquareHom_isIntegral eS))
      (_hplacesT : ∀ y : closedPoints (projectiveLineRatFuncModel κ).C,
        ∃ hy : pT.base y.val ∈ closedPoints (projectiveLineRatFuncModel κ).C,
          (projectiveLineRatFuncModel κ).placeOfPoint ⟨pT.base y.val, hy⟩ =
            ((projectiveLineRatFuncModel κ).placeOfPoint y).restrictAlong
              (ratFuncPairSquareHom eT) (ratFuncPairSquareHom_isIntegral eT))
      (pSE pTE : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
      (eSE eTE : RatFunc E ≃ₐ[E] RatFunc E)
      (_heSE : eSE RatFunc.X = algebraMap (RatFunc k) (RatFunc E) f)
      (_heTE : eTE RatFunc.X = algebraMap (RatFunc k) (RatFunc E) g)
      (_hcoeffS : pS ≫ map E κ 1 = map E κ 1 ≫ pSE)
      (_hcoeffT : pT ≫ map E κ 1 = map E κ 1 ≫ pTE)
      (_hplacesSE : ∀ y : closedPoints (projectiveLineRatFuncModel E).C,
        ∃ hy : pSE.base y.val ∈ closedPoints (projectiveLineRatFuncModel E).C,
          (projectiveLineRatFuncModel E).placeOfPoint ⟨pSE.base y.val, hy⟩ =
            ((projectiveLineRatFuncModel E).placeOfPoint y).restrictAlong
              (ratFuncPairSquareHom eSE) (ratFuncPairSquareHom_isIntegral eSE))
      (_hplacesTE : ∀ y : closedPoints (projectiveLineRatFuncModel E).C,
        ∃ hy : pTE.base y.val ∈ closedPoints (projectiveLineRatFuncModel E).C,
          (projectiveLineRatFuncModel E).placeOfPoint ⟨pTE.base y.val, hy⟩ =
            ((projectiveLineRatFuncModel E).placeOfPoint y).restrictAlong
              (ratFuncPairSquareHom eTE) (ratFuncPairSquareHom_isIntegral eTE))
      (_hlabelsS : ∀ z, z ∈ tS ↔ projectiveRationalPoint z ∉ Set.range
        (Limits.pullback.fst pSE (rationalConfigurationBaseChangeChart k E s)))
      (_hlabelsT : ∀ z, z ∈ tT ↔ projectiveRationalPoint z ∉ Set.range
        (Limits.pullback.fst pTE (rationalConfigurationBaseChangeChart k E t))),
    ∃ F : (k × k) ≃ₗ[k] (k × k),
      (∀ p : s, projectiveLinearEquiv F p.val = (σ p).val) ∧
      ∃ I : (rationalConfigurationOpen s : Scheme) ≅ (rationalConfigurationOpen t : Scheme),
        I.hom ≫ (rationalConfigurationOpen t).ι =
          (rationalConfigurationOpen s).ι ≫ (pairLinearCoordinateIso F).hom ∧
        I.hom ≫ ((rationalConfigurationOpen t).ι ≫ π k 1) =
          (rationalConfigurationOpen s).ι ≫ π k 1 := by
  intro fs ft xs xt ys yt bs bt hs0 ht0 cs ct φ bκS bκT GS GT hGS hGT hNS hNT hLS0 hLT0
    aS aT AS AT hclosureS hclosureT instS instT ξS ξT hpointS hpointT c αE αc hstrict
    WES WET hconnES hconnET instES instET ec hfiber wE wET WS WT hconnS hconnT instWS instWT
    wS wT tS tT JS JT qES qET hJS hJT hstructS hstructT
    JκS JκT eS eT pS pT hjκS hjκT instjS instjT
    hboundaryS hboundaryT hcardS hcardT hfieldS hfieldT AMS AMT instMS instMT qκS qκT
    hmodelS hmodelT hgeomS hgeomT hmodelarithS hmodelarithT hqκcoeffS hqκcoeffT
    hplacesS hplacesT pSE pTE eSE eTE heSE heTE hcoeffS hcoeffT hplacesSE hplacesTE
    hlabelsS hlabelsT
  obtain ⟨αΔ, hαΔ, βP, hβP, βΔ, hβΔ, hsquareκ⟩ :=
    namedSquareModels_actual_projections_exists_geometric_square
      (modelASΩ := AMS) (modelATΩ := AMT) E κ cs ct ξS ξT
      WES WET tS tT ys yt hpointS hpointT αc hstrict ec hfiber wE JS JT qES qET
      hJS hJT hstructS hstructT hmodelarithS hmodelarithT
      qκS qκT hqκcoeffS hqκcoeffT hgeomS hgeomT
  have HLS := namedSquare_matchedModel_exists_literal_model k E κ s Ω₁ WS wS tS JκS eS pS
    hboundaryS hfieldS hmodelS
  have HLT := namedSquare_matchedModel_exists_literal_model k E κ t Ω₂ WT wT tT JκT eT pT
    hboundaryT hfieldT hmodelT
  let isoS := namedSquareConstantProjectionIso k E κ s
  let isoT := namedSquareConstantProjectionIso k E κ t
  let ALS : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁ :=
    namedBaseTransportAmbientAlgebra isoS Ω₁
  let ALT : Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂ :=
    namedBaseTransportAmbientAlgebra isoT Ω₂
  let WLS := namedCoverOnIsomorphicBase isoS WS
  let WLT := namedCoverOnIsomorphicBase isoT WT
  let : CategoryTheory.PreGaloisCategory.IsConnected WLS :=
    namedCoverOnIsomorphicBase_isConnected isoS WS
  let : CategoryTheory.PreGaloisCategory.IsConnected WLT :=
    namedCoverOnIsomorphicBase_isConnected isoT WT
  obtain ⟨hclosureLS, wLS, _hwLS, hJLS, hboundaryLS, hfieldLS, hmodelLS, hgeomLS⟩ := HLS
  obtain ⟨hclosureLT, wLT, _hwLT, hJLT, hboundaryLT, hfieldLT, hmodelLT, hgeomLT⟩ := HLT
  let : IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω₁ := hclosureLS
  let : IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ω₂ := hclosureLT
  let ξLS := (rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω₁
  let ξLT := (rationalConfigurationGeometricScheme k κ t).genericExtensionMorphism Ω₂
  have hgenS : ξS ≫ isoS.hom = ξLS := namedBaseTransport_genericPoint isoS Ω₁
  have hgenT : ξT ≫ isoT.hom = ξLT := namedBaseTransport_genericPoint isoT Ω₂
  have hcardS' : s.card ≤ tS.card := by
    simpa only [namedSquareConstantProjectionChart_boundary_card k E κ s] using hcardS
  have hcardT' : t.card ≤ tT.card := by
    simpa only [namedSquareConstantProjectionChart_boundary_card k E κ t] using hcardT
  have htS : 3 ≤ tS.card := hs.trans hcardS'
  have htT : 3 ≤ tT.card := ht.trans hcardT'
  let uS := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ))) fs
  let uT := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ))) ft
  have hisoS : isoS.hom ≫ uS = bκS ≫ bs := namedSquareConstantProjectionIso_snd k E κ s
  have hisoT : isoT.hom ≫ uT = bκT ≫ bt := namedSquareConstantProjectionIso_snd k E κ t
  have hLS := namedBaseTransport_point_projection_of_factorization
    isoS ξS ξLS hgenS uS bκS bs hisoS ys xs hpointS hs0
  have hLT := namedBaseTransport_point_projection_of_factorization
    isoT ξT ξLT hgenT uT bκT bt hisoT yt xt hpointT ht0
  let αL := namedBaseTransport_pointedGeometricMap isoS isoT ξS ξT ξLS ξLT hgenS hgenT αΔ
  let iT := pointedFundamentalGroupHom bt yt xt ht0
  let c₀arith := iT c
  have hraw := finiteBase_corrected_geometricMap_original_square k E κ
    fs ft xs xt eP hP ξS ξT hpointS hpointT c αΔ hαΔ
  have hαL := namedBaseTransport_pointedGeometricMap_factored_conjugate_square
    isoS isoT ξS ξT ξLS ξLT hgenS hgenT uS uT ys yt xs xt hLS hLT
    bκS bκT bs bt hpointS hpointT hs0 ht0 hisoS hisoT αΔ eP c₀arith hraw
  let qLS := JκS.inv ≫ WLS.hom
  let qLT := JκT.inv ≫ WLT.hom
  have hqLS : qκS ≫ isoS.hom = qLS := Category.assoc _ _ _
  have hqLT : qκT ≫ isoT.hom = qLT := Category.assoc _ _ _
  have hsquareL := namedBaseTransport_pointedGeometricMap_cover_square_of_eq
    isoS isoT ξS ξT ξLS ξLT hgenS hgenT
    ((rationalConfigurationGeometricScheme E κ tS).genericExtensionMorphism Ω₁)
    ((rationalConfigurationGeometricScheme E κ tT).genericExtensionMorphism Ω₂)
    qκS qκT hgeomS hgeomT αΔ βΔ hsquareκ qLS qLT hqLS hqLT hgeomLS hgeomLT
  have hIL := by
    as_aux_lemma =>
      exact rationalConfiguration_correctedMatchedMap_same_punctures
        (AS₀ := AoldS) (AT₀ := AoldT) (HS₀ := HoldS) (HT₀ := HoldT)
        k κ s t ht Ω₁ Ω₂ eP eΔ hΔ σ hI ALS ALT hclosureLS hclosureLT
        hLS hLT αL c₀arith hαL
  exact nakamura_reconstruct_literal_models
    k E κ s t tS tT ht htS htT
    Ω₁ WLS wLS JκS qLS hJLS pS eS hplacesS hboundaryLS hfieldLS
    Ω₂ WLT wLT JκT qLT hJLT pT eT hplacesT hboundaryLT hfieldLT
    pSE eSE hcoeffS hplacesSE hlabelsS pTE eTE hcoeffT hplacesTE hlabelsT
    AMS AMT hmodelLS hmodelLT hgeomLS hgeomLT αL βP hβP βΔ hβΔ σ hIL hsquareL
    hclasses a b c₀ hab h₀a h₀b VS₀ VSinf VT₀ VTinf
    f g hf hg heSE heTE harithS harithT hgeomf hgeomg rS rT hrS hrT

/-- Reconstruct the projective transformation while retaining the geometric
fundamental-group comparison and the inertia characterization of its puncture
bijection. These are the comparisons needed for descent of the same map. -/
theorem exists_projectiveTransformation_with_inertia_of_arithmeticFundamentalGroupEquiv
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [AoldS : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [AoldT : Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    [HoldS : IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [HoldT : IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (eP : rationalConfigurationArithmeticGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ω₂)
    (hP : ∀ γ,
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ t Ω₂) (eP γ) =
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ s Ω₁) γ) :
    ∃ eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
        rationalConfigurationGeometricGroup k κ t Ω₂,
      (∀ v, rationalConfigurationGeometricInclusion k κ t Ω₂ (eΔ v) =
        eP (rationalConfigurationGeometricInclusion k κ s Ω₁ v)) ∧
      ∃ σ : s ≃ t,
        (∀ p : s, ∃ a : rationalConfigurationGeometricGroup k κ t Ω₂,
          (rationalConfigurationChosenInertia k κ s Ω₁
            (rationalConfigurationBoundaryPlace k κ s p)).map eΔ.toMonoidHom =
          (rationalConfigurationChosenInertia k κ t Ω₂
            (rationalConfigurationBoundaryPlace k κ t (σ p))).map
              (MulAut.conj a).toMonoidHom) ∧
        ∃ f : (k × k) ≃ₗ[k] (k × k),
      (∀ p : s, projectiveLinearEquiv f p.val = (σ p).val) ∧
      ∃ I : (rationalConfigurationOpen s : Scheme) ≅ (rationalConfigurationOpen t : Scheme),
        I.hom ≫ (rationalConfigurationOpen t).ι =
          (rationalConfigurationOpen s).ι ≫ (pairLinearCoordinateIso f).hom ∧
        I.hom ≫ ((rationalConfigurationOpen t).ι ≫ π k 1) =
          (rationalConfigurationOpen s).ι ≫ π k 1 := by
  classical
  obtain ⟨eΔ, hΔ, σ, hI, hclasses, hpairs⟩ :=
    bare_rationalConfiguration_same_punctures_pointed_square_data k κ s t hs ht Ω₁ Ω₂ eP hP
  have hthree : Fintype.card (Fin 3) ≤ Fintype.card s := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hs
  obtain ⟨ι⟩ : Nonempty (Fin 3 ↪ s) := Function.Embedding.nonempty_of_card_le hthree
  let a : s := ι 0
  let b : s := ι 1
  let c₀ : s := ι 2
  have hab : a ≠ b := fun h => (by decide : (0 : Fin 3) ≠ 1) (ι.injective h)
  have h₀a : c₀ ≠ a := fun h => (by decide : (2 : Fin 3) ≠ 0) (ι.injective h)
  have h₀b : c₀ ≠ b := fun h => (by decide : (2 : Fin 3) ≠ 1) (ι.injective h)
  obtain ⟨VS₀, VSinf, VT₀, VTinf, f, g, hf, hg, harithS, harithT, hgeomf, hgeomg,
    us, ut, _ws, _wt, hus, hut, _hws, _hwt, _hvector, _hresidue, _htransport, _hscalar,
    _hsquare, ρS, ρT, _hρS, _hρT, H⟩ := hpairs a b
  subst f
  subst g
  let fs := (rationalConfigurationOpen s).ι ≫ π k 1
  let ft := (rationalConfigurationOpen t).ι ≫ π k 1
  let xs := rationalConfigurationArithmeticBasePoint k κ s Ω₁
  let xt := rationalConfigurationArithmeticBasePoint k κ t Ω₂
  let hn : IsUnit ((2 : ℕ) : k) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (show (2 : ℕ) ≠ 0 from by decide))
  let M := projectiveLineRatFuncModel k
  let AS := M.openKummerCover (M.openBoundaryPlaces (rationalConfigurationOpen s).ι)
    (2 : ℕ+) hn us (rationalConfigurationOpen s).ι
    (rationalConfigurationOpen_denseRange k s)
    (M.place_not_mem_openBoundaryPlaces (rationalConfigurationOpen s).ι)
  let AT := M.openKummerCover (M.openBoundaryPlaces (rationalConfigurationOpen t).ι)
    (2 : ℕ+) hn ut (rationalConfigurationOpen t).ι
    (rationalConfigurationOpen_denseRange k t)
    (M.place_not_mem_openBoundaryPlaces (rationalConfigurationOpen t).ι)
  obtain ⟨scalar, βroot, _hβroot, H⟩ := H
  let E := quadraticBoundaryCoordinateField k κ βroot (Sum.elim ρS ρT)
  let : FiniteDimensional k E :=
    quadraticBoundaryCoordinateField_finiteDimensional k κ βroot (Sum.elim ρS ρT)
  let : NumberField E := NumberField.of_module_finite k E
  let : Algebra.IsAlgebraic E κ :=
    Algebra.IsAlgebraic.tower_top (K := k) (L := E) (A := κ)
  let : IsAlgClosure E κ := ⟨inferInstance, inferInstance⟩
  let : Algebra.IsSeparable k E := inferInstance
  let : IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
    constantField_specMap_isFiniteEtale k E
  let : IsSepClosure E κ :=
    ⟨IsSepClosure.sep_closed k, Algebra.isSeparable_tower_top_of_isSeparable k E κ⟩
  let ys : Spec (.of Ω₁) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k E))) fs :=
    arithmeticConstantFieldLift k E κ fs xs
  let yt : Spec (.of Ω₂) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k E))) ft :=
    arithmeticConstantFieldLift k E κ ft xt
  let bs : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) fs ⟶
      (rationalConfigurationOpen s : Scheme) :=
    ((FiniteEtale.pullback fs).obj (originalConstantFieldCover k E)).hom
  let bt : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) ft ⟶
      (rationalConfigurationOpen t : Scheme) :=
    ((FiniteEtale.pullback ft).obj (originalConstantFieldCover k E)).hom
  let hs0 := arithmeticConstantFieldLift_comp k E κ fs xs
  let ht0 := arithmeticConstantFieldLift_comp k E κ ft xt
  obtain ⟨rS, rT, _hrSκ, _hrTκ, hrS, hrT, θ, x₀, H⟩ := H
  let wE : (fiber ys).obj ((FiniteEtale.pullback bs).obj AS) :=
    (pointedPullbackFiberEquiv bs ys xs hs0 AS).symm
      (coverTransportFiberEquiv (fiber xs) (fiber xt) eP AS x₀)
  let cs : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) fs ⟶
      Spec (.of E) :=
    Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) fs
  let ct : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) ft ⟶
      Spec (.of E) :=
    Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) ft
  let φ : Spec (.of κ) ⟶ Spec (.of E) := Spec.map (CommRingCat.ofHom (algebraMap E κ))
  let GS := Limits.pullback φ cs
  let GT := Limits.pullback φ ct
  let : IsIntegral GS := rationalConfiguration_coefficientTower_isIntegral k E κ s
  let : IsIntegral GT := rationalConfiguration_coefficientTower_isIntegral k E κ t
  obtain ⟨jS, aS, _jT, aT, _hjS, _hjT, H⟩ := H
  let A_S : Algebra GS.functionField Ω₁ := aS.toAlgebra
  let A_T : Algebra GT.functionField Ω₂ := aT.toAlgebra
  obtain ⟨hclosureS, hclosureT, _hcoefS, _hcoefT, hpointS, hpointT, c,
    hstrict, hfiber, hsourcePoint⟩ := H
  let : IsAlgClosure GS.functionField Ω₁ := hclosureS
  let : IsAlgClosure GT.functionField Ω₂ := hclosureT
  let eE := namedSquareFiniteBaseFiberEquiv bs bt ys yt xs xt hs0 ht0 eP AS AT θ
  let ec : (fiber ys).obj ((FiniteEtale.pullback bs).obj AS) ≃
      (fiber yt).obj ((FiniteEtale.pullback bt).obj AT) :=
    ProCGroups.innerCorrectedFiberEquiv eE c
  let wET := ec wE
  obtain ⟨eSE, eS, heSE, _heS, pSE, hpSE, _hfiniteSE, hplacesSE, _JmodelS, _hJmodelS,
    hconnES, tS, hlabelsS, JS, qES, hJS, _hqES, hstructS, _hambientS,
    hcoeffS, hconnS, JκS, _hJκcoeffS, _hJκbaseS, hplacesS, hboundaryS, hcardS,
    hqκcoeffS, _hqκbaseS, hjκS, hfieldS, hmodelS, hmodelarithS, hgeomS⟩ :=
    namedSquare_pair_matchedPoint_exists_actual_model k E κ s hn us a b hab
      VS₀ VSinf harithS hgeomf rS hrS Ω₁ aS ys hpointS wE
  obtain ⟨eTE, eT, heTE, _heT, pTE, hpTE, _hfiniteTE, hplacesTE, _JmodelT, _hJmodelT,
    hconnET, tT, hlabelsT, JT, qET, hJT, _hqET, hstructT, _hambientT,
    hcoeffT, hconnT, JκT, _hJκcoeffT, _hJκbaseT, hplacesT, hboundaryT, hcardT,
    hqκcoeffT, _hqκbaseT, hjκT, hfieldT, hmodelT, hmodelarithT, hgeomT⟩ :=
    namedSquare_pair_matchedPoint_exists_actual_model k E κ t hn ut (σ a) (σ b)
      (σ.injective.ne hab) VT₀ VTinf harithT hgeomg rT hrT Ω₂ aT yt hpointT wET
  let WES : FiniteEtale (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) fs) :=
    (FiniteEtale.pullback bs).obj AS
  let WET : FiniteEtale (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) ft) :=
    (FiniteEtale.pullback bt).obj AT
  let bκS := Limits.pullback.snd φ cs
  let bκT := Limits.pullback.snd φ ct
  let WS : FiniteEtale GS := (FiniteEtale.pullback bκS).obj WES
  let WT : FiniteEtale GT := (FiniteEtale.pullback bκT).obj WET
  let ξS : Spec (.of Ω₁) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap E κ))) cs :=
    GS.genericExtensionMorphism Ω₁
  let ξT : Spec (.of Ω₂) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap E κ))) ct :=
    GT.genericExtensionMorphism Ω₂
  let wS := (pointedPullbackFiberEquiv bκS ξS ys hpointS WES).symm wE
  let wT := (pointedPullbackFiberEquiv bκT ξT yt hpointT WET).symm wET
  let : CategoryTheory.PreGaloisCategory.IsConnected WES := hconnES
  let : CategoryTheory.PreGaloisCategory.IsConnected WET := hconnET
  let : CategoryTheory.PreGaloisCategory.IsConnected WS := hconnS
  let : CategoryTheory.PreGaloisCategory.IsConnected WT := hconnT
  let : IsNormalIntegral GS := namedSquareMatchedBase_isNormalIntegral k E κ s
  let : IsNormalIntegral GT := namedSquareMatchedBase_isNormalIntegral k E κ t
  let : IsLocallyNoetherian GS := namedSquareMatchedBase_isLocallyNoetherian k E κ s
  let : IsLocallyNoetherian GT := namedSquareMatchedBase_isLocallyNoetherian k E κ t
  let : IsOpenImmersion (namedSquareConstantProjectionChart k E κ s) := hjκS
  let : IsOpenImmersion (namedSquareConstantProjectionChart k E κ t) := hjκT
  let AMS : Algebra (rationalConfigurationGeometricScheme E κ tS).functionField Ω₁ :=
    namedSquareModelAmbientAlgebra WS wS JκS
  let AMT : Algebra (rationalConfigurationGeometricScheme E κ tT).functionField Ω₂ :=
    namedSquareModelAmbientAlgebra WT wT JκT
  let pS := Limits.baseChangedModelMap (isPullback_map E κ 1) pSE hpSE
  let pT := Limits.baseChangedModelMap (isPullback_map E κ 1) pTE hpTE
  obtain ⟨F, hlinear, I, hambient, hover⟩ := nakamura_finish_named_models
    (AoldS := AoldS) (AoldT := AoldT) (HoldS := HoldS) (HoldT := HoldT)
    k E κ s t hs ht Ω₁ Ω₂ eP hP eΔ hΔ σ hI hclasses
    a b c₀ hab h₀a h₀b VS₀.val VSinf.val VT₀.val VTinf.val
    (us.val : RatFunc k) (ut.val : RatFunc k) hf hg harithS harithT hgeomf hgeomg rS rT hrS hrT
    aS aT hclosureS hclosureT hpointS hpointT c hstrict
    WES WET hconnES hconnET ec hfiber wE hconnS hconnT
    tS tT JS JT qES qET hJS hJT hstructS hstructT JκS JκT eS eT pS pT hjκS hjκT
    hboundaryS hboundaryT hcardS hcardT hfieldS hfieldT AMS AMT
    hmodelS hmodelT hgeomS hgeomT hmodelarithS hmodelarithT hqκcoeffS hqκcoeffT hplacesS hplacesT
    pSE pTE eSE eTE heSE heTE hcoeffS hcoeffT hplacesSE hplacesTE hlabelsS hlabelsT
  exact ⟨eΔ, hΔ, σ, hI, F, hlinear, I, hambient, hover⟩

/-- The weak reconstruction theorem, with its original conclusion. -/
theorem exists_projectiveTransformation_of_arithmeticFundamentalGroupEquiv
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (eP : rationalConfigurationArithmeticGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ω₂)
    (hP : ∀ γ,
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ t Ω₂) (eP γ) =
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ s Ω₁) γ) :
    ∃ (σ : s ≃ t) (f : (k × k) ≃ₗ[k] (k × k)),
      (∀ p : s, projectiveLinearEquiv f p.val = (σ p).val) ∧
      ∃ I : (rationalConfigurationOpen s : Scheme) ≅ (rationalConfigurationOpen t : Scheme),
        I.hom ≫ (rationalConfigurationOpen t).ι =
          (rationalConfigurationOpen s).ι ≫ (pairLinearCoordinateIso f).hom ∧
        I.hom ≫ ((rationalConfigurationOpen t).ι ≫ π k 1) =
          (rationalConfigurationOpen s).ι ≫ π k 1 := by
  obtain ⟨_eΔ, _hΔ, σ, _hI, f, hf, I, hambient, hover⟩ :=
    exists_projectiveTransformation_with_inertia_of_arithmeticFundamentalGroupEquiv
      k κ s t hs ht Ω₁ Ω₂ eP hP
  exact ⟨σ, f, hf, I, hambient, hover⟩

end AnabelianGeometry.WeightFiltration
