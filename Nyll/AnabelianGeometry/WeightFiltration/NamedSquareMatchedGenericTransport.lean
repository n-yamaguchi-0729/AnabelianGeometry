/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareCanonicalFiniteBaseTransport
import Nyll.AnabelianGeometry.WeightFiltration.MatchedConstantGenericAmbient
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticScalarCanonicalBaseEquivariance
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticConstantFieldStrictTransport

/-! # Matched generic transport over the canonical finite base -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open scoped FintypeCatDiscrete
namespace AnabelianGeometry.WeightFiltration

attribute [local instance] connectedCoverTarget

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ]
  [IsSepClosure k κ] [IsSepClosed κ]
variable (E : IntermediateField k κ) [IsSepClosure E κ] [Algebra.IsAlgebraic E κ]
  [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
variable {Xs Xt : Scheme} [IsIntegral Xs] [IsIntegral Xt]
  [ConnectedSpace Xs] [ConnectedSpace Xt]
variable (fs : Xs ⟶ Spec (.of k)) (ft : Xt ⟶ Spec (.of k))
  [GeometricallyConnected ft]
variable {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
variable [IsAlgClosed Ωs] [IsAlgClosed Ωt]
variable [Algebra Xs.functionField Ωs] [IsAlgClosure Xs.functionField Ωs]
variable [Algebra Xt.functionField Ωt] [IsAlgClosure Xt.functionField Ωt]
variable [IsIntegral (Limits.pullback
  (Spec.map (CommRingCat.ofHom (algebraMap k E))) fs)]
variable [IsIntegral (Limits.pullback
  (Spec.map (CommRingCat.ofHom (algebraMap k E))) ft)]
variable [IsIntegral (Limits.pullback
  (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
  (Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) fs))]
variable [IsIntegral (Limits.pullback
  (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
  (Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) ft))]
variable (α : π₁ᵉᵗ((Xs.genericExtensionMorphism Ωs)) ≃ₜ* π₁ᵉᵗ((Xt.genericExtensionMorphism Ωt)))
variable (hα : ∀ g, arithmeticFundamentalGroupHom k κ ft (Xt.genericExtensionMorphism Ωt) (α g) =
  arithmeticFundamentalGroupHom k κ fs (Xs.genericExtensionMorphism Ωs) g)
variable (AS : FiniteEtale Xs) (AT : FiniteEtale Xt)

theorem namedSquare_exists_matchedGeneric_strictFiberTransport
    [Torsor (rootsOfUnity 2 κ)
      ((fiber (Xt.genericExtensionMorphism Ωt)).obj ((coverTransportOfAutEquiv (fiber
        (Xs.genericExtensionMorphism Ωs)) (fiber (Xt.genericExtensionMorphism Ωt)) α).functor.obj
        AS))]
    [Torsor (rootsOfUnity 2 κ) ((fiber (Xt.genericExtensionMorphism Ωt)).obj AT)]
    (hS : ∀ (p : π₁ᵉᵗ((Xt.genericExtensionMorphism Ωt))) (ζ : rootsOfUnity 2 κ)
        (x : (fiber (Xt.genericExtensionMorphism Ωt)).obj
          ((coverTransportOfAutEquiv (fiber (Xs.genericExtensionMorphism Ωs)) (fiber
            (Xt.genericExtensionMorphism Ωt)) α).functor.obj AS)),
      p • (ζ • x) = restrictRootsOfUnity
        (arithmeticFundamentalGroupHom k κ ft (Xt.genericExtensionMorphism Ωt) p).toRingHom 2 ζ •
          (p • x))
    (hT : ∀ (p : π₁ᵉᵗ((Xt.genericExtensionMorphism Ωt))) (ζ : rootsOfUnity 2 κ) (x : (fiber
      (Xt.genericExtensionMorphism Ωt)).obj AT),
      p • (ζ • x) = restrictRootsOfUnity
        (arithmeticFundamentalGroupHom k κ ft (Xt.genericExtensionMorphism Ωt) p).toRingHom 2 ζ •
          (p • x))
    (θ : (fiber (Xt.genericExtensionMorphism Ωt)).obj
        ((coverTransportOfAutEquiv (fiber (Xs.genericExtensionMorphism Ωs)) (fiber
          (Xt.genericExtensionMorphism Ωt)) α).functor.obj AS) ≃
      (fiber (Xt.genericExtensionMorphism Ωt)).obj AT)
    (hθμ : ∀ (ζ : rootsOfUnity 2 κ) x, θ (ζ • x) = ζ • θ x)
    (x₀ : (fiber (Xt.genericExtensionMorphism Ωt)).obj
      ((coverTransportOfAutEquiv (fiber (Xs.genericExtensionMorphism Ωs)) (fiber
        (Xt.genericExtensionMorphism Ωt)) α).functor.obj AS))
    (β : κˣ) (hβE : (β : κ) ∈ E)
    (hdisp : ∀ p : π₁ᵉᵗ((Xt.genericExtensionMorphism Ωt)),
      _root_.KummerTheory.rootQuotient (K := k) β
        (arithmeticFundamentalGroupHom k κ ft (Xt.genericExtensionMorphism Ωt) p) =
          ((p • θ (p⁻¹ • x₀)) /ₛ θ x₀ : rootsOfUnity 2 κ).val) :
    let bs := ((pullback fs).obj (originalConstantFieldCover k E)).hom
    let bt := ((pullback ft).obj (originalConstantFieldCover k E)).hom
    let ys := arithmeticConstantFieldLift k E κ fs (Xs.genericExtensionMorphism Ωs)
    let yt := arithmeticConstantFieldLift k E κ ft (Xt.genericExtensionMorphism Ωt)
    let hs := arithmeticConstantFieldLift_comp k E κ fs (Xs.genericExtensionMorphism Ωs)
    let ht := arithmeticConstantFieldLift_comp k E κ ft (Xt.genericExtensionMorphism Ωt)
    let iS := pointedFundamentalGroupHom bs ys (Xs.genericExtensionMorphism Ωs) hs
    let iT := pointedFundamentalGroupHom bt yt (Xt.genericExtensionMorphism Ωt) ht
    let αE := arithmeticConstantFieldCoverGroupTransport k E κ fs ft (Xs.genericExtensionMorphism
      Ωs) (Xt.genericExtensionMorphism Ωt) α hα
    let eE := namedSquareFiniteBaseFiberEquiv bs bt ys yt (Xs.genericExtensionMorphism Ωs)
      (Xt.genericExtensionMorphism Ωt) hs ht α AS AT θ
    let cs := Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) fs
    let ct := Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) ft
    let GS := Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) cs
    let GT := Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) ct
    ∃ (jS : κ →+* Ωs) (aS : GS.functionField →+* Ωs)
      (jT : κ →+* Ωt) (aT : GT.functionField →+* Ωt),
      jS.comp (algebraMap E κ) = (Spec.preimage (ys ≫ cs)).hom ∧
      jT.comp (algebraMap E κ) = (Spec.preimage (yt ≫ ct)).hom ∧
      let _A_S : Algebra GS.functionField Ωs := aS.toAlgebra
      let _A_T : Algebra GT.functionField Ωt := aT.toAlgebra
      IsAlgClosure GS.functionField Ωs ∧ IsAlgClosure GT.functionField Ωt ∧
      GS.genericExtensionMorphism Ωs ≫ Limits.pullback.fst _ cs =
        Spec.map (CommRingCat.ofHom jS) ∧
      GT.genericExtensionMorphism Ωt ≫ Limits.pullback.fst _ ct =
        Spec.map (CommRingCat.ofHom jT) ∧
      GS.genericExtensionMorphism Ωs ≫ Limits.pullback.snd _ cs = ys ∧
      GT.genericExtensionMorphism Ωt ≫ Limits.pullback.snd _ ct = yt ∧
    ∃ c : π₁ᵉᵗ(yt),
      (∀ g, arithmeticFundamentalGroupHom E κ
          (Limits.pullback.fst (originalConstantFieldCover k E).hom ft) yt
          (ProCGroups.innerCorrectedGroupEquiv αE c g) =
        arithmeticFundamentalGroupHom E κ
          (Limits.pullback.fst (originalConstantFieldCover k E).hom fs) ys g) ∧
      (∀ g x, ProCGroups.innerCorrectedFiberEquiv eE c (g • x) =
        ProCGroups.innerCorrectedGroupEquiv αE c g •
          ProCGroups.innerCorrectedFiberEquiv eE c x) ∧
      (∀ g, iT (ProCGroups.innerCorrectedGroupEquiv αE c g) =
        iT c * α (iS g) * (iT c)⁻¹) := by
  intro bs bt ys yt hs ht iS iT αE eE cs ct GS GT
  obtain ⟨jS, aS, hjS, hSambient⟩ := exists_matchedConstant_genericAmbient
    k E κ fs Ωs (arithmeticConstantFieldFiberPoint k E κ fs (Xs.genericExtensionMorphism Ωs))
  obtain ⟨jT, aT, hjT, hTambient⟩ := exists_matchedConstant_genericAmbient
    k E κ ft Ωt (arithmeticConstantFieldFiberPoint k E κ ft (Xt.genericExtensionMorphism Ωt))
  refine ⟨jS, aS, jT, aT, hjS, hjT, ?_⟩
  intro A_S A_T
  obtain ⟨hclS, hcoefS, hpointS⟩ := hSambient
  obtain ⟨hclT, hcoefT, hpointT⟩ := hTambient
  refine ⟨hclS, hclT, hcoefS, hcoefT, hpointS, hpointT, ?_⟩
  exact namedSquare_exists_canonicalFiniteBase_strictFiberTransport
    k κ E fs ft (Xs.genericExtensionMorphism Ωs) (Xt.genericExtensionMorphism Ωt) α hα AS AT hS hT
      θ hθμ x₀ β hβE hdisp

end AnabelianGeometry.WeightFiltration
