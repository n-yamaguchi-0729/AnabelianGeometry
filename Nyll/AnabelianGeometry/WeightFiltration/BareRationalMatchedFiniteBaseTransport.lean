/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.RationalConfigurationMatchedGenericAmbient
import Nyll.AnabelianGeometry.WeightFiltration.ArithmeticMatchedConstantStrictTransport
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineGeometry

/-! Matched generic points and strict transport after a finite extension of constants. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
namespace AnabelianGeometry.WeightFiltration
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

theorem bare_rationalConfiguration_exists_matched_finiteBase_strict_transport
    (k E κ : Type) [Field k] [NumberField k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsAlgClosure k κ] [IsAlgClosed κ] [CharZero κ]
    [Algebra.IsAlgebraic E κ] [IsSepClosure E κ]
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
    (s t : Finset (Projectivization k (k × k)))
    (Ωs Ωt : Type) [Field Ωs] [Field Ωt] [IsAlgClosed Ωs] [IsAlgClosed Ωt]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ωs]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ωt]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ωs]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ωt]
    (α : rationalConfigurationArithmeticGroup k κ s Ωs ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ωt)
    (hα : ∀ g, arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ t Ωt) (α g) =
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ s Ωs) g) :
    let fs := (rationalConfigurationOpen s).ι ≫ π k 1
    let ft := (rationalConfigurationOpen t).ι ≫ π k 1
    let xs := rationalConfigurationArithmeticBasePoint k κ s Ωs
    let xt := rationalConfigurationArithmeticBasePoint k κ t Ωt
    let ys := arithmeticConstantFieldLift k E κ fs xs
    let yt := arithmeticConstantFieldLift k E κ ft xt
    let cs := pullback.fst (originalConstantFieldCover k E).hom fs
    let ct := pullback.fst (originalConstantFieldCover k E).hom ft
    let GS := pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) cs
    let GT := pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) ct
    let _hGS : IsIntegral GS := rationalConfiguration_coefficientTower_isIntegral k E κ s
    let _hGT : IsIntegral GT := rationalConfiguration_coefficientTower_isIntegral k E κ t
    let αE := arithmeticConstantFieldCoverGroupTransport k E κ fs ft xs xt α hα
    ∃ (jS : κ →+* Ωs) (aS : GS.functionField →+* Ωs)
      (jT : κ →+* Ωt) (aT : GT.functionField →+* Ωt),
      jS.comp (algebraMap E κ) = (Spec.preimage (ys ≫ cs)).hom ∧
      jT.comp (algebraMap E κ) = (Spec.preimage (yt ≫ ct)).hom ∧
      let _A_S : Algebra GS.functionField Ωs := aS.toAlgebra
      let _A_T : Algebra GT.functionField Ωt := aT.toAlgebra
      IsAlgClosure GS.functionField Ωs ∧ IsAlgClosure GT.functionField Ωt ∧
      GS.genericExtensionMorphism Ωs ≫ pullback.fst _ cs =
        Spec.map (CommRingCat.ofHom jS) ∧
      GT.genericExtensionMorphism Ωt ≫ pullback.fst _ ct =
        Spec.map (CommRingCat.ofHom jT) ∧
      GS.genericExtensionMorphism Ωs ≫ pullback.snd _ cs = ys ∧
      GT.genericExtensionMorphism Ωt ≫ pullback.snd _ ct = yt ∧
      ∃ c : π₁ᵉᵗ(yt),
        arithmeticFundamentalGroupHom E κ ct yt c =
          (arithmeticConstantFieldComparisonOverE k E κ ft xt *
            (arithmeticConstantFieldComparisonOverE k E κ fs xs)⁻¹)⁻¹ ∧
        ∀ g, arithmeticFundamentalGroupHom E κ ct yt
          (ProCGroups.innerCorrectedGroupEquiv αE c g) =
            arithmeticFundamentalGroupHom E κ cs ys g := by
  intro fs ft xs xt ys yt cs ct GS GT hGS hGT αE
  obtain ⟨jS, aS, hjS, hS⟩ := rationalConfiguration_exists_matchedConstant_genericAmbient
    k E κ s Ωs (arithmeticConstantFieldFiberPoint k E κ fs xs)
  obtain ⟨jT, aT, hjT, hT⟩ := rationalConfiguration_exists_matchedConstant_genericAmbient
    k E κ t Ωt (arithmeticConstantFieldFiberPoint k E κ ft xt)
  refine ⟨jS, aS, jT, aT, hjS, hjT, ?_⟩
  intro A_S A_T
  obtain ⟨hclS, hcoefS, hpointS⟩ := hS
  obtain ⟨hclT, hcoefT, hpointT⟩ := hT
  refine ⟨hclS, hclT, hcoefS, hcoefT, hpointS, hpointT, ?_⟩
  have : CompactSpace ((FiniteEtale.pullback ft).obj
      (originalConstantFieldCover k E)).left :=
    QuasiCompact.compactSpace_of_compactSpace
      (show _ ⟶ (rationalConfigurationOpen t : Scheme) from
        ((FiniteEtale.pullback ft).obj (originalConstantFieldCover k E)).hom)
  have : QuasiSeparatedSpace ((FiniteEtale.pullback ft).obj
      (originalConstantFieldCover k E)).left :=
    quasiSeparatedSpace_of_quasiSeparated
      (show _ ⟶ (rationalConfigurationOpen t : Scheme) from
        ((FiniteEtale.pullback ft).obj (originalConstantFieldCover k E)).hom)
  exact exists_arithmeticConstantFieldCover_strict_transport_of_matchedLift
    k E κ fs ft xs xt α hα (GT.genericExtensionMorphism Ωt) hpointT

end AnabelianGeometry.WeightFiltration
