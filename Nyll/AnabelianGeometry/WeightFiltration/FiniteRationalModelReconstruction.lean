/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.SchemeIsomorphism
import Nyll.AnabelianGeometry.WeightFiltration.RationalConfigurationBasePoint
import Nyll.AnabelianGeometry.WeightFiltration.RationalConfigurationNakamura
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticConstantFieldStrictTransport
import Nyll.ProCGroups.Topologies.ArithmeticInnerCorrectionFiberTransport

/-! # Reconstruction at actual finite rational models

The arithmetic isomorphism on the original curves is restricted to the actual
constant covers. Its correction over the finite field and the two pullbacks
along the actual model isomorphisms are retained. In particular the resulting
rational-configuration isomorphism is not an independently chosen weak
isomorphism. This file does not assert Galois descent of the resulting map.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open AnabelianGeometry.ArithmeticIsomorphisms AnabelianGeometry.ProjectiveLine

namespace AnabelianGeometry.WeightFiltration

/-- Pass from the original arithmetic groups to the canonical generic groups
of two actual rational models over a finite constant field. Both fibre
comparisons and the exact finite-cover correction are part of the conclusion. -/
theorem exists_rationalModel_arithmetic_transport
    (k E κ : Type) [Field k] [Field E] [NumberField E]
    [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsAlgClosure E κ]
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
    {Xs Xt : Scheme} [ConnectedSpace Xs] [ConnectedSpace Xt]
    (fs : Xs ⟶ Spec (.of k)) (ft : Xt ⟶ Spec (.of k)) [GeometricallyConnected ft]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (xis : Spec (.of Ωs) ⟶ Xs) (xit : Spec (.of Ωt) ⟶ Xt)
    (s t : Finset (Projectivization E (E × E)))
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme E κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme E κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme E κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme E κ t).functionField Ω₂]
    (Js : ((pullback fs).obj (originalConstantFieldCover k E)).left ≅
      (rationalConfigurationOpen s : Scheme))
    (Jt : ((pullback ft).obj (originalConstantFieldCover k E)).left ≅
      (rationalConfigurationOpen t : Scheme))
    (hJs : Js.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
      Limits.pullback.fst (originalConstantFieldCover k E).hom fs)
    (hJt : Jt.hom ≫ ((rationalConfigurationOpen t).ι ≫ π E 1) =
      Limits.pullback.fst (originalConstantFieldCover k E).hom ft)
    (α : π₁ᵉᵗ(xis) ≃ₜ* π₁ᵉᵗ(xit))
    (hα : ∀ g, arithmeticFundamentalGroupHom k κ ft xit (α g) =
      arithmeticFundamentalGroupHom k κ fs xis g) :
    let xsE := arithmeticConstantFieldLift k E κ fs xis
    let xtE := arithmeticConstantFieldLift k E κ ft xit
    let xs := rationalConfigurationArithmeticBasePoint E κ s Ω₁
    let xt := rationalConfigurationArithmeticBasePoint E κ t Ω₂
    ∃ (c : π₁ᵉᵗ(xtE))
      (es : π₁ᵉᵗ(xsE) ≃ₜ* rationalConfigurationArithmeticGroup E κ s Ω₁)
      (et : π₁ᵉᵗ(xtE) ≃ₜ* rationalConfigurationArithmeticGroup E κ t Ω₂),
      arithmeticFundamentalGroupHom E κ
          (Limits.pullback.fst (originalConstantFieldCover k E).hom ft) xtE c =
        (arithmeticConstantFieldComparisonOverE k E κ ft xit *
          (arithmeticConstantFieldComparisonOverE k E κ fs xis)⁻¹)⁻¹ ∧
      (∃ ts : fiber (xsE ≫ Js.hom) ≅ fiber xs,
        ∀ g, es g = continuousConjAut ts (fundamentalGroupHom Js.hom xsE g)) ∧
      (∃ tt : fiber (xtE ≫ Jt.hom) ≅ fiber xt,
        ∀ g, et g = continuousConjAut tt (fundamentalGroupHom Jt.hom xtE g)) ∧
      (∀ g, arithmeticFundamentalGroupHom E κ
          ((rationalConfigurationOpen s).ι ≫ π E 1) xs (es g) =
        arithmeticFundamentalGroupHom E κ
          (Limits.pullback.fst (originalConstantFieldCover k E).hom fs) xsE g) ∧
      (∀ g, arithmeticFundamentalGroupHom E κ
          ((rationalConfigurationOpen t).ι ≫ π E 1) xt (et g) =
        arithmeticFundamentalGroupHom E κ
          (Limits.pullback.fst (originalConstantFieldCover k E).hom ft) xtE g) ∧
      ∀ g : rationalConfigurationArithmeticGroup E κ s Ω₁,
        arithmeticFundamentalGroupHom E κ
            ((rationalConfigurationOpen t).ι ≫ π E 1) xt
            (et (ProCGroups.innerCorrectedGroupEquiv
              (arithmeticConstantFieldCoverGroupTransport k E κ fs ft xis xit α hα)
              c (es.symm g))) =
          arithmeticFundamentalGroupHom E κ
            ((rationalConfigurationOpen s).ι ≫ π E 1) xs g := by
  intro xsE xtE xs xt
  have : IsSepClosure E κ := ⟨inferInstance, inferInstance⟩
  let gs := (rationalConfigurationOpen s).ι ≫ π E 1
  let gt := (rationalConfigurationOpen t).ι ≫ π E 1
  have : GeometricallyConnected gs := rationalConfigurationOpen_geometricallyConnected E s
  have : GeometricallyConnected gt := rationalConfigurationOpen_geometricallyConnected E t
  obtain ⟨c, hc, htransport⟩ := exists_arithmeticConstantFieldCover_strict_transport
    k E κ fs ft xis xit α hα
  obtain ⟨es, hes, hqs⟩ := exists_arithmetic_groupEquiv_of_schemeIso E κ
    (Limits.pullback.fst (originalConstantFieldCover k E).hom fs) gs Js hJs xsE xs
  obtain ⟨et, het, hqt⟩ := exists_arithmetic_groupEquiv_of_schemeIso E κ
    (Limits.pullback.fst (originalConstantFieldCover k E).hom ft) gt Jt hJt xtE xt
  refine ⟨c, es, et, hc, hes, het, hqs, hqt, fun g => ?_⟩
  exact (hqt _).trans ((htransport _).trans
    ((hqs (es.symm g)).symm.trans
      (congrArg (arithmeticFundamentalGroupHom E κ gs xs) (es.apply_symm_apply g))))

/-- Reconstruct over the finite field from the original arithmetic isomorphism
and actual split models. The same puncture bijection is characterized by the
geometric inertia groups of the transported isomorphism. This retains the
information needed to compare its Galois translates; no descent assertion is
made here. -/
theorem exists_projectiveTransformation_of_constantCover_models
    (k E κ : Type) [Field k] [Field E] [NumberField E]
    [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsAlgClosure E κ]
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
    {Xs Xt : Scheme} [ConnectedSpace Xs] [ConnectedSpace Xt]
    (fs : Xs ⟶ Spec (.of k)) (ft : Xt ⟶ Spec (.of k)) [GeometricallyConnected ft]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (xis : Spec (.of Ωs) ⟶ Xs) (xit : Spec (.of Ωt) ⟶ Xt)
    (s t : Finset (Projectivization E (E × E))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme E κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme E κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme E κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme E κ t).functionField Ω₂]
    (Js : ((pullback fs).obj (originalConstantFieldCover k E)).left ≅
      (rationalConfigurationOpen s : Scheme))
    (Jt : ((pullback ft).obj (originalConstantFieldCover k E)).left ≅
      (rationalConfigurationOpen t : Scheme))
    (hJs : Js.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
      Limits.pullback.fst (originalConstantFieldCover k E).hom fs)
    (hJt : Jt.hom ≫ ((rationalConfigurationOpen t).ι ≫ π E 1) =
      Limits.pullback.fst (originalConstantFieldCover k E).hom ft)
    (α : π₁ᵉᵗ(xis) ≃ₜ* π₁ᵉᵗ(xit))
    (hα : ∀ g, arithmeticFundamentalGroupHom k κ ft xit (α g) =
      arithmeticFundamentalGroupHom k κ fs xis g) :
    let xsE := arithmeticConstantFieldLift k E κ fs xis
    let xtE := arithmeticConstantFieldLift k E κ ft xit
    let xs := rationalConfigurationArithmeticBasePoint E κ s Ω₁
    let xt := rationalConfigurationArithmeticBasePoint E κ t Ω₂
    ∃ (c : π₁ᵉᵗ(xtE))
      (es : π₁ᵉᵗ(xsE) ≃ₜ* rationalConfigurationArithmeticGroup E κ s Ω₁)
      (et : π₁ᵉᵗ(xtE) ≃ₜ* rationalConfigurationArithmeticGroup E κ t Ω₂),
      (∃ ts : fiber (xsE ≫ Js.hom) ≅ fiber xs,
        ∀ g, es g = continuousConjAut ts (fundamentalGroupHom Js.hom xsE g)) ∧
      (∃ tt : fiber (xtE ≫ Jt.hom) ≅ fiber xt,
        ∀ g, et g = continuousConjAut tt (fundamentalGroupHom Jt.hom xtE g)) ∧
      arithmeticFundamentalGroupHom E κ
          (Limits.pullback.fst (originalConstantFieldCover k E).hom ft) xtE c =
        (arithmeticConstantFieldComparisonOverE k E κ ft xit *
          (arithmeticConstantFieldComparisonOverE k E κ fs xis)⁻¹)⁻¹ ∧
      let β := es.symm.trans
        ((ProCGroups.innerCorrectedGroupEquiv
          (arithmeticConstantFieldCoverGroupTransport k E κ fs ft xis xit α hα) c).trans et)
      ∃ eΔ : rationalConfigurationGeometricGroup E κ s Ω₁ ≃ₜ*
          rationalConfigurationGeometricGroup E κ t Ω₂,
        (∀ v, rationalConfigurationGeometricInclusion E κ t Ω₂ (eΔ v) =
          β (rationalConfigurationGeometricInclusion E κ s Ω₁ v)) ∧
        ∃ σ : s ≃ t,
          (∀ p : s, ∃ a : rationalConfigurationGeometricGroup E κ t Ω₂,
            (rationalConfigurationChosenInertia E κ s Ω₁
              (rationalConfigurationBoundaryPlace E κ s p)).map eΔ.toMonoidHom =
            (rationalConfigurationChosenInertia E κ t Ω₂
              (rationalConfigurationBoundaryPlace E κ t (σ p))).map
                (MulAut.conj a).toMonoidHom) ∧
          ∃ f : (E × E) ≃ₗ[E] (E × E),
            (∀ p : s, projectiveLinearEquiv f p.val = (σ p).val) ∧
            ∃ I : ((pullback fs).obj (originalConstantFieldCover k E)).left ≅
                ((pullback ft).obj (originalConstantFieldCover k E)).left,
              I.hom ≫ Jt.hom ≫ (rationalConfigurationOpen t).ι =
                Js.hom ≫ (rationalConfigurationOpen s).ι ≫ (pairLinearCoordinateIso f).hom ∧
              I.hom ≫ Limits.pullback.fst (originalConstantFieldCover k E).hom ft =
                Limits.pullback.fst (originalConstantFieldCover k E).hom fs := by
  intro xsE xtE xs xt
  obtain ⟨c, es, et, hc, hes, het, _hqs, _hqt, hβ⟩ :=
    exists_rationalModel_arithmetic_transport k E κ fs ft xis xit s t Ω₁ Ω₂ Js Jt hJs hJt α hα
  let β := es.symm.trans
    ((ProCGroups.innerCorrectedGroupEquiv
      (arithmeticConstantFieldCoverGroupTransport k E κ fs ft xis xit α hα) c).trans et)
  obtain ⟨eΔ, hΔ, σ, hI, f, hf, J, hJ, hJbase⟩ :=
    exists_projectiveTransformation_with_inertia_of_arithmeticFundamentalGroupEquiv
      E κ s t hs ht Ω₁ Ω₂ β hβ
  let I := Js ≪≫ J ≪≫ Jt.symm
  refine ⟨c, es, et, hes, het, hc, eΔ, hΔ, σ, hI, f, hf, I, ?_, ?_⟩
  · change ((Js.hom ≫ J.hom) ≫ Jt.inv) ≫ Jt.hom ≫ _ = _
    rw [Category.assoc, Jt.inv_hom_id_assoc, Category.assoc, hJ]
  · have hJtinv : Jt.inv ≫ Limits.pullback.fst
        (originalConstantFieldCover k E).hom ft =
        (rationalConfigurationOpen t).ι ≫ π E 1 := by
      exact (congrArg (fun q => Jt.inv ≫ q) hJt.symm).trans
        (Jt.inv_hom_id_assoc ((rationalConfigurationOpen t).ι ≫ π E 1))
    change ((Js.hom ≫ J.hom) ≫ Jt.inv) ≫ _ = _
    exact (Category.assoc (Js.hom ≫ J.hom) Jt.inv _).trans
      ((congrArg (fun q => (Js.hom ≫ J.hom) ≫ q) hJtinv).trans
        ((Category.assoc Js.hom J.hom _).trans
          ((congrArg (fun q => Js.hom ≫ q) hJbase).trans hJs)))

end AnabelianGeometry.WeightFiltration
