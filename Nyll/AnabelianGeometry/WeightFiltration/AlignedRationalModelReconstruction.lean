/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.AlignedRationalModelAmbient
import Nyll.AnabelianGeometry.WeightFiltration.RationalConfigurationNakamura
import Nyll.AnabelianGeometry.WeightFiltration.NamedModelCoverGroupSquare
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticConstantFieldStrictTransport
import Nyll.EtaleFundamentalGroups.GeometricFiber.MatchedFiberArithmeticCoverTransport

/-! # Split reconstruction through the actual matched rational models

The point equalities here are supplied by
`exists_alignedRationalModel_genericAmbient`. They make the model comparisons
literal pointed maps. The same finite-cover correction, geometric comparison,
and inertia bijection are retained, before any Galois descent is asserted.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open AlgebraicGeometry.ProjSpace AnabelianGeometry.ProjectiveLine

namespace AnabelianGeometry.WeightFiltration

/-- Apply split reconstruction to the actual pointed finite models. The only
inner correction is the computed correction in the native target cover. -/
theorem exists_projectiveTransformation_of_pointed_constantCover_models
    (k E κ : Type) [Field k] [Field E] [NumberField E]
    [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsAlgClosure E κ]
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
    {Xs Xt : Scheme} [ConnectedSpace Xs] [ConnectedSpace Xt]
    (fs : Xs ⟶ Spec (.of k)) (ft : Xt ⟶ Spec (.of k)) [GeometricallyConnected ft]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsAlgClosed Ωs] [IsAlgClosed Ωt]
    (xis : Spec (.of Ωs) ⟶ Xs) (xit : Spec (.of Ωt) ⟶ Xt)
    (s t : Finset (Projectivization E (E × E))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    [Algebra (rationalConfigurationGeometricScheme E κ s).functionField Ωs]
    [Algebra (rationalConfigurationGeometricScheme E κ t).functionField Ωt]
    [IsAlgClosure (rationalConfigurationGeometricScheme E κ s).functionField Ωs]
    [IsAlgClosure (rationalConfigurationGeometricScheme E κ t).functionField Ωt]
    (Js : ((pullback fs).obj (originalConstantFieldCover k E)).left ≅
      (rationalConfigurationOpen s : Scheme))
    (Jt : ((pullback ft).obj (originalConstantFieldCover k E)).left ≅
      (rationalConfigurationOpen t : Scheme))
    (hJs : Js.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
      Limits.pullback.fst (originalConstantFieldCover k E).hom fs)
    (hJt : Jt.hom ≫ ((rationalConfigurationOpen t).ι ≫ π E 1) =
      Limits.pullback.fst (originalConstantFieldCover k E).hom ft)
    (hxs : arithmeticConstantFieldLift k E κ fs xis ≫ Js.hom =
      rationalConfigurationArithmeticBasePoint E κ s Ωs)
    (hxt : arithmeticConstantFieldLift k E κ ft xit ≫ Jt.hom =
      rationalConfigurationArithmeticBasePoint E κ t Ωt)
    (α : π₁ᵉᵗ(xis) ≃ₜ* π₁ᵉᵗ(xit))
    (hα : ∀ g, arithmeticFundamentalGroupHom k κ ft xit (α g) =
      arithmeticFundamentalGroupHom k κ fs xis g) :
    let xsE := arithmeticConstantFieldLift k E κ fs xis
    let xtE := arithmeticConstantFieldLift k E κ ft xit
    let xs := rationalConfigurationArithmeticBasePoint E κ s Ωs
    let xt := rationalConfigurationArithmeticBasePoint E κ t Ωt
    let _hconnS : ConnectedSpace (((pullback fs).obj (originalConstantFieldCover k E)).left) :=
      Js.hom.homeomorph.connectedSpace_iff.mpr inferInstance
    let _hconnT : ConnectedSpace (((pullback ft).obj (originalConstantFieldCover k E)).left) :=
      Jt.hom.homeomorph.connectedSpace_iff.mpr inferInstance
    let es := namedModelPointedGroupEquiv Js xsE xs hxs
    let et := namedModelPointedGroupEquiv Jt xtE xt hxt
    ∃ c : π₁ᵉᵗ(xtE),
      arithmeticFundamentalGroupHom E κ
          (Limits.pullback.fst (originalConstantFieldCover k E).hom ft) xtE c =
        (arithmeticConstantFieldComparisonOverE k E κ ft xit *
          (arithmeticConstantFieldComparisonOverE k E κ fs xis)⁻¹)⁻¹ ∧
      let β := es.symm.trans
        ((ProCGroups.innerCorrectedGroupEquiv
          (arithmeticConstantFieldCoverGroupTransport k E κ fs ft xis xit α hα) c).trans et)
      ∃ eΔ : rationalConfigurationGeometricGroup E κ s Ωs ≃ₜ*
          rationalConfigurationGeometricGroup E κ t Ωt,
        (∀ v, rationalConfigurationGeometricInclusion E κ t Ωt (eΔ v) =
          β (rationalConfigurationGeometricInclusion E κ s Ωs v)) ∧
        ∃ σ : s ≃ t,
          (∀ p : s, ∃ a : rationalConfigurationGeometricGroup E κ t Ωt,
            (rationalConfigurationChosenInertia E κ s Ωs
              (rationalConfigurationBoundaryPlace E κ s p)).map eΔ.toMonoidHom =
            (rationalConfigurationChosenInertia E κ t Ωt
              (rationalConfigurationBoundaryPlace E κ t (σ p))).map
                (MulAut.conj a).toMonoidHom) ∧
          ∃ f : (E × E) ≃ₗ[E] (E × E),
            (∀ p : s, projectiveLinearEquiv f p.val = (σ p).val) ∧
            ∃ I : (rationalConfigurationOpen s : Scheme) ≅
                (rationalConfigurationOpen t : Scheme),
              I.hom ≫ (rationalConfigurationOpen t).ι =
                (rationalConfigurationOpen s).ι ≫ (pairLinearCoordinateIso f).hom ∧
              I.hom ≫ ((rationalConfigurationOpen t).ι ≫ π E 1) =
                (rationalConfigurationOpen s).ι ≫ π E 1 := by
  intro xsE xtE xs xt hconnS hconnT es et
  have : IsSepClosure E κ := ⟨inferInstance, inferInstance⟩
  obtain ⟨c, hc, htransport⟩ := exists_arithmeticConstantFieldCover_strict_transport
    k E κ fs ft xis xit α hα
  have hqs (g : π₁ᵉᵗ(xsE)) :
      arithmeticFundamentalGroupHom E κ ((rationalConfigurationOpen s).ι ≫ π E 1)
        xs (es g) = arithmeticFundamentalGroupHom E κ
          (Limits.pullback.fst (originalConstantFieldCover k E).hom fs) xsE g := by
    rw [namedModelPointedGroupEquiv_apply,
      arithmeticFundamentalGroupHom_pointed_comp, hJs]
    rfl
  have hqt (g : π₁ᵉᵗ(xtE)) :
      arithmeticFundamentalGroupHom E κ ((rationalConfigurationOpen t).ι ≫ π E 1)
        xt (et g) = arithmeticFundamentalGroupHom E κ
          (Limits.pullback.fst (originalConstantFieldCover k E).hom ft) xtE g := by
    rw [namedModelPointedGroupEquiv_apply,
      arithmeticFundamentalGroupHom_pointed_comp, hJt]
    rfl
  let β := es.symm.trans
    ((ProCGroups.innerCorrectedGroupEquiv
      (arithmeticConstantFieldCoverGroupTransport k E κ fs ft xis xit α hα) c).trans et)
  have hβ (g : rationalConfigurationArithmeticGroup E κ s Ωs) :
      arithmeticFundamentalGroupHom E κ ((rationalConfigurationOpen t).ι ≫ π E 1)
          xt (β g) =
        arithmeticFundamentalGroupHom E κ ((rationalConfigurationOpen s).ι ≫ π E 1)
          xs g :=
    (hqt _).trans ((htransport _).trans ((hqs (es.symm g)).symm.trans
      (congrArg (arithmeticFundamentalGroupHom E κ
        ((rationalConfigurationOpen s).ι ≫ π E 1) xs) (es.apply_symm_apply g))))
  exact ⟨c, hc,
    exists_projectiveTransformation_with_inertia_of_arithmeticFundamentalGroupEquiv
      E κ s t hs ht Ωs Ωt β hβ⟩

end AnabelianGeometry.WeightFiltration
