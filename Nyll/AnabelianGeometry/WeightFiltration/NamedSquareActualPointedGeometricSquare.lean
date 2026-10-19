/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareMatchedPointModel
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareMatchedGeometricSquare
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareFiniteBaseFiberTransport
import Nyll.AnabelianGeometry.WeightFiltration.NamedModelCoverGroupSquare
import Nyll.AnabelianGeometry.WeightFiltration.RationalConfigurationMatchedGenericAmbient
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineGeometry
import Nyll.EtaleFundamentalGroups.GeometricFiber.RecoveredCoverGenericPoint
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalConfigurationCuspRecognition
import Nyll.EtaleFundamentalGroups.GeometricFiber.MatchedFiberCoverGroupTransport
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral

/-! # Geometric squares from the actual points of matched covers -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace EtaleFundamentalGroups
open scoped FintypeCatDiscrete
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AnabelianGeometry.WeightFiltration

local instance actualPointedSquareOverCategory (S : Scheme) :
    Category (MorphismProperty.Over (@IsFiniteEtale : MorphismProperty Scheme) ⊤ S) :=
  AlgebraicGeometry.FiniteEtale.instCategory S
local instance actualPointedSquareHasPullbacksAlong {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun _ _ ↦ inferInstance⟩
local instance actualPointedSquareStableUnderBaseChangeAlong {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme)) h hf⟩

theorem namedSquareModels_actual_projections_exists_geometric_square
    (E κ : Type) [Field E] [Field κ] [Algebra E κ] [IsSepClosure E κ]
    [CharZero κ] [IsAlgClosed κ] [Infinite E]
    {XS XT : Scheme} [ConnectedSpace XS] [ConnectedSpace XT]
    [CompactSpace XS] [QuasiSeparatedSpace XS]
    [CompactSpace XT] [QuasiSeparatedSpace XT]
    (fs : XS ⟶ Spec (.of E)) (ft : XT ⟶ Spec (.of E))
    [ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) fs : Scheme)]
    [ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) ft : Scheme)]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (xs : Spec (.of Ωs) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) fs)
    (xt : Spec (.of Ωt) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) ft)
    (AS : FiniteEtale XS) (AT : FiniteEtale XT) [CategoryTheory.PreGaloisCategory.IsConnected AS]
    [CategoryTheory.PreGaloisCategory.IsConnected AT]
    (s t : Finset (Projectivization E (E × E)))
    [modelASΩ : Algebra (rationalConfigurationGeometricScheme E κ s).functionField Ωs]
    [modelATΩ : Algebra (rationalConfigurationGeometricScheme E κ t).functionField Ωt]
    (ys : Spec (.of Ωs) ⟶ XS) (yt : Spec (.of Ωt) ⟶ XT)
    (hxs : xs ≫ pullback.snd _ fs = ys) (hxt : xt ≫ pullback.snd _ ft = yt)
    (α : π₁ᵉᵗ(ys) ≃ₜ* π₁ᵉᵗ(yt))
    (hα : ∀ z, arithmeticFundamentalGroupHom E κ ft yt (α z) =
      arithmeticFundamentalGroupHom E κ fs ys z)
    (e : (fiber ys).obj AS ≃
      (fiber yt).obj AT)
    (he : fiberEquivariant ys yt AS AT α e)
    (w : (fiber ys).obj AS)
    (JS : AS.left ≅ (rationalConfigurationOpen s : Scheme))
    (JT : AT.left ≅ (rationalConfigurationOpen t : Scheme))
    (qs : (rationalConfigurationOpen s : Scheme) ⟶ XS)
    (qt : (rationalConfigurationOpen t : Scheme) ⟶ XT)
    (hJS : JS.hom ≫ qs = AS.hom) (hJT : JT.hom ≫ qt = AT.hom)
    (hstructS : qs ≫ fs = (rationalConfigurationOpen s).ι ≫ π E 1)
    (hstructT : qt ≫ ft = (rationalConfigurationOpen t).ι ≫ π E 1)
    (hmodelarithS : rationalConfigurationArithmeticBasePoint E κ s Ωs =
      namedModelPoint AS ys w JS)
    (hmodelarithT : rationalConfigurationArithmeticBasePoint E κ t Ωt =
      namedModelPoint AT yt (e w) JT)
    (qκs : rationalConfigurationGeometricScheme E κ s ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) fs)
    (qκt : rationalConfigurationGeometricScheme E κ t ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) ft)
    (hcoeffS : qκs ≫ pullback.snd _ fs =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
        ((rationalConfigurationOpen s).ι ≫ π E 1) ≫ qs)
    (hcoeffT : qκt ≫ pullback.snd _ ft =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
        ((rationalConfigurationOpen t).ι ≫ π E 1) ≫ qt)
    (hgeomS : (rationalConfigurationGeometricScheme E κ s).genericExtensionMorphism Ωs ≫
      qκs = xs)
    (hgeomT : (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ωt ≫
      qκt = xt) :
    ∃ αΔ : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt),
      (∀ z, pointedFundamentalGroupHom (pullback.snd _ ft) xt yt hxt (αΔ z) =
        α (pointedFundamentalGroupHom (pullback.snd _ fs) xs ys hxs z)) ∧
      ∃ αR : rationalConfigurationArithmeticGroup E κ s Ωs ≃ₜ*
          rationalConfigurationArithmeticGroup E κ t Ωt,
        (∀ z, arithmeticFundamentalGroupHom E κ ((rationalConfigurationOpen t).ι ≫ π E 1)
            (rationalConfigurationArithmeticBasePoint E κ t Ωt) (αR z) =
          arithmeticFundamentalGroupHom E κ ((rationalConfigurationOpen s).ι ≫ π E 1)
            (rationalConfigurationArithmeticBasePoint E κ s Ωs) z) ∧
      ∃ βΔ : rationalConfigurationGeometricGroup E κ s Ωs ≃ₜ*
          rationalConfigurationGeometricGroup E κ t Ωt,
        (∀ z, rationalConfigurationGeometricInclusion E κ t Ωt (βΔ z) =
          αR (rationalConfigurationGeometricInclusion E κ s Ωs z)) ∧
        ∀ z, pointedFundamentalGroupHom qκt
            ((rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ωt)
            xt hgeomT (βΔ z) =
          αΔ (pointedFundamentalGroupHom qκs
            ((rationalConfigurationGeometricScheme E κ s).genericExtensionMorphism Ωs)
            xs hgeomS z) := by
  change ∀ z v, e (z • v) = α z • e v at he
  subst ys
  subst yt
  obtain ⟨αΔ, hαΔ, βP, hβP, βΔ, hβΔ, hsquare⟩ :=
    namedSquareModels_exists_geometric_square_of_matched_points E κ fs ft xs xt
      AS AT s t (xs ≫ pullback.snd _ fs) (xt ≫ pullback.snd _ ft)
      rfl rfl α hα e he w JS JT qs qt
      hJS hJT hstructS hstructT hmodelarithS hmodelarithT
      qκs qκt hcoeffS hcoeffT hgeomS hgeomT
  exact ⟨αΔ, hαΔ, βP, hβP, βΔ, hβΔ, hsquare⟩

theorem namedSquareModels_actual_points_exists_geometric_square
    (k E κ : Type) [Field k] [Field E] [Field κ] [Infinite k] [Infinite E]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure E κ] [CharZero κ] [IsAlgClosed κ]
    (s₀ t₀ : Finset (Projectivization k (k × k)))
    (Ωs Ωt : Type) [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt] :
    let cs := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      ((rationalConfigurationOpen s₀).ι ≫ π k 1)
    let ct := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      ((rationalConfigurationOpen t₀).ι ≫ π k 1)
    let φ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
    let bs := pullback.snd φ cs
    let bt := pullback.snd φ ct
    let GS := pullback φ cs
    let GT := pullback φ ct
    let _hGS : IsIntegral GS := rationalConfiguration_coefficientTower_isIntegral k E κ s₀
    let _hGT : IsIntegral GT := rationalConfiguration_coefficientTower_isIntegral k E κ t₀
    let _hNormalS : IsNormalIntegral GS := namedSquareMatchedBase_isNormalIntegral k E κ s₀
    let _hNormalT : IsNormalIntegral GT := namedSquareMatchedBase_isNormalIntegral k E κ t₀
    let _hNoetherianS : IsLocallyNoetherian GS :=
      namedSquareMatchedBase_isLocallyNoetherian k E κ s₀
    let _hNoetherianT : IsLocallyNoetherian GT :=
      namedSquareMatchedBase_isLocallyNoetherian k E κ t₀
    ∀ (aΩs : GS.functionField →+* Ωs) (aΩt : GT.functionField →+* Ωt),
    let _ASΩ : Algebra GS.functionField Ωs := aΩs.toAlgebra
    let _ATΩ : Algebra GT.functionField Ωt := aΩt.toAlgebra
    let xs := GS.genericExtensionMorphism Ωs
    let xt := GT.genericExtensionMorphism Ωt
    ∀ (ys : Spec (.of Ωs) ⟶ rationalConfigurationGeometricScheme k E s₀)
      (yt : Spec (.of Ωt) ⟶ rationalConfigurationGeometricScheme k E t₀)
      (hxs : xs ≫ bs = ys) (hxt : xt ≫ bt = yt)
      (AS : FiniteEtale (rationalConfigurationGeometricScheme k E s₀))
      (AT : FiniteEtale (rationalConfigurationGeometricScheme k E t₀))
      (hconnES : CategoryTheory.PreGaloisCategory.IsConnected AS)
      (hconnET : CategoryTheory.PreGaloisCategory.IsConnected AT),
    let _ := hconnES
    let _ := hconnET
    ∀ (α : π₁ᵉᵗ(ys) ≃ₜ* π₁ᵉᵗ(yt))
      (_hα : ∀ z, arithmeticFundamentalGroupHom E κ ct yt (α z) =
        arithmeticFundamentalGroupHom E κ cs ys z)
      (e : (fiber ys).obj AS ≃ (fiber yt).obj AT)
      (_he : fiberEquivariant ys yt AS AT α e)
      (w : (fiber ys).obj AS)
      (s t : Finset (Projectivization E (E × E)))
      (JS : AS.left ≅ (rationalConfigurationOpen s : Scheme))
      (JT : AT.left ≅ (rationalConfigurationOpen t : Scheme))
      (qs : (rationalConfigurationOpen s : Scheme) ⟶ rationalConfigurationGeometricScheme k E s₀)
      (qt : (rationalConfigurationOpen t : Scheme) ⟶ rationalConfigurationGeometricScheme k E t₀)
      (_hJS : JS.hom ≫ qs = AS.hom) (_hJT : JT.hom ≫ qt = AT.hom)
      (_hstructS : qs ≫ cs = (rationalConfigurationOpen s).ι ≫ π E 1)
      (_hstructT : qt ≫ ct = (rationalConfigurationOpen t).ι ≫ π E 1),
    let WS := (FiniteEtale.pullback bs).obj AS
    let WT := (FiniteEtale.pullback bt).obj AT
    let wS := (pointedPullbackFiberEquiv bs xs ys hxs AS).symm w
    let wT := (pointedPullbackFiberEquiv bt xt yt hxt AT).symm (e w)
    ∀ (hconnS : CategoryTheory.PreGaloisCategory.IsConnected WS)
      (hconnT : CategoryTheory.PreGaloisCategory.IsConnected WT),
    let _ := hconnS
    let _ := hconnT
    ∀ (JκS : WS.left ≅ rationalConfigurationGeometricScheme E κ s)
      (JκT : WT.left ≅ rationalConfigurationGeometricScheme E κ t),
    let qκS := JκS.inv ≫ WS.hom
    let qκT := JκT.inv ≫ WT.hom
    ∀ (_hcoeffS : qκS ≫ bs =
        pullback.snd φ ((rationalConfigurationOpen s).ι ≫ π E 1) ≫ qs)
      (_hcoeffT : qκT ≫ bt =
        pullback.snd φ ((rationalConfigurationOpen t).ι ≫ π E 1) ≫ qt),
    let _hIntegralS : IsIntegral WS.left := isIntegral_left_of_isConnected_finiteEtale WS
    let _hIntegralT : IsIntegral WT.left := isIntegral_left_of_isConnected_finiteEtale WT
    let _AKLS : Algebra GS.functionField WS.left.functionField := finiteEtaleFunctionFieldAlgebra WS
    let _AKLT : Algebra GT.functionField WT.left.functionField := finiteEtaleFunctionFieldAlgebra WT
    let liftS := fiberObjEquivHom xs WS wS
    let liftT := fiberObjEquivHom xt WT wT
    let embS := finiteEtaleGenericHomFunctionFieldAlgHom WS liftS
    let embT := finiteEtaleGenericHomFunctionFieldAlgHom WT liftT
    let _ANΩS : Algebra (rationalConfigurationGeometricScheme E κ s).functionField Ωs :=
      (embS.toRingHom.comp
        (JκS.hom.functionFieldMap JκS.hom.homeomorph.surjective.denseRange)).toAlgebra
    let _ANΩT : Algebra (rationalConfigurationGeometricScheme E κ t).functionField Ωt :=
      (embT.toRingHom.comp
        (JκT.hom.functionFieldMap JκT.hom.homeomorph.surjective.denseRange)).toAlgebra
    ∀ (_hmodelarithS : rationalConfigurationArithmeticBasePoint E κ s Ωs =
        namedModelPoint AS ys w JS)
      (_hmodelarithT : rationalConfigurationArithmeticBasePoint E κ t Ωt =
        namedModelPoint AT yt (e w) JT)
      (hgeomS : (rationalConfigurationGeometricScheme E κ s).genericExtensionMorphism Ωs ≫ qκS = xs)
      (hgeomT : (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ωt ≫ qκT =
        xt),
    ∃ αΔ : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt),
      (∀ z, pointedFundamentalGroupHom bt xt yt hxt (αΔ z) =
        α (pointedFundamentalGroupHom bs xs ys hxs z)) ∧
    ∃ βP : rationalConfigurationArithmeticGroup E κ s Ωs ≃ₜ*
        rationalConfigurationArithmeticGroup E κ t Ωt,
      (∀ z, arithmeticFundamentalGroupHom E κ ((rationalConfigurationOpen t).ι ≫ π E 1)
          (rationalConfigurationArithmeticBasePoint E κ t Ωt) (βP z) =
        arithmeticFundamentalGroupHom E κ ((rationalConfigurationOpen s).ι ≫ π E 1)
          (rationalConfigurationArithmeticBasePoint E κ s Ωs) z) ∧
    ∃ βΔ : rationalConfigurationGeometricGroup E κ s Ωs ≃ₜ*
        rationalConfigurationGeometricGroup E κ t Ωt,
      (∀ z, rationalConfigurationGeometricInclusion E κ t Ωt (βΔ z) =
        βP (rationalConfigurationGeometricInclusion E κ s Ωs z)) ∧
      ∀ z, pointedFundamentalGroupHom qκT
          ((rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ωt)
          xt hgeomT (βΔ z) =
        αΔ (pointedFundamentalGroupHom qκS
          ((rationalConfigurationGeometricScheme E κ s).genericExtensionMorphism Ωs)
          xs hgeomS z) := by
  intro cs ct φ bs bt GS GT hGS hGT hNormalS hNormalT hNoetherianS hNoetherianT
    aΩs aΩt ASΩ ATΩ xs xt ys yt hxs hxt AS AT hconnES hconnET instES instET α hα e he w s t
    JS JT qs qt hJS hJT hstructS hstructT WS WT wS wT hconnS hconnT
    instS instT JκS JκT qκS qκT hcoeffS hcoeffT hIntegralS hIntegralT
    AKLS AKLT liftS liftT embS embT ANΩS ANΩT hmodelarithS hmodelarithT hgeomS hgeomT
  exact namedSquareModels_actual_projections_exists_geometric_square
    E κ cs ct xs xt AS AT s t ys yt hxs hxt α hα e he w JS JT qs qt
    hJS hJT hstructS hstructT hmodelarithS hmodelarithT
    qκS qκT hcoeffS hcoeffT hgeomS hgeomT

end AnabelianGeometry.WeightFiltration
