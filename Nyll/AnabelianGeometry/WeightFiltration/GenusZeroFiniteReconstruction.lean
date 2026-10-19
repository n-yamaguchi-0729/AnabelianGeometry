/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.GenusZeroFiniteModels
import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.GeometricBasePoint
import Nyll.AnabelianGeometry.WeightFiltration.AlignedRationalModelAmbient
import Nyll.AnabelianGeometry.WeightFiltration.ArithmeticAlignedCoefficientEmbedding
import Nyll.AnabelianGeometry.WeightFiltration.AlignedRationalModelReconstruction
import Nyll.SchemeTheory.FunctionFields.GeometricIntegrality
import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleConnected

/-! # Finite reconstruction from the original genus-zero opens

The ambient fields are the algebraic closures of the original function fields.
Arithmetic-preserving fiber comparisons move the supplied isomorphism to these
generic points. The coefficient embeddings are aligned before the actual
finite rational models are used. The conclusion retains their ambient squares,
the literal point comparisons, and the same correction and reconstruction
produced by the split theorem, for subsequent Galois descent.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open AnabelianGeometry.ArithmeticIsomorphisms
open AnabelianGeometry.GeometricFundamentalGroup AnabelianGeometry.ProjectiveLine

namespace AnabelianGeometry.WeightFiltration

private theorem exists_aligned_fiber_comparisons
    (k κ Ω₁ Ω₂ : Type) [Field k] [Field κ] [Field Ω₁] [Field Ω₂]
    [Algebra k κ] [IsSepClosure k κ] [IsSepClosed κ]
    [IsAlgClosed Ω₁] [IsAlgClosed Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    {X₁ X₂ : Scheme}
    (f₁ : X₁ ⟶ Spec (.of k)) (f₂ : X₂ ⟶ Spec (.of k))
    [GeometricallyConnected f₁] [GeometricallyConnected f₂]
    {Λ₁ Λ₂ : Type} [Field Λ₁] [Field Λ₂] [IsSepClosed Λ₁] [IsSepClosed Λ₂]
    (x₁ : Spec (.of Λ₁) ⟶ X₁) (x₂ : Spec (.of Λ₂) ⟶ X₂)
    (xi₁ : Spec (.of Ω₁) ⟶ X₁) (xi₂ : Spec (.of Ω₂) ⟶ X₂)
    (eP : π₁ᵉᵗ(x₁) ≃ₜ* π₁ᵉᵗ(x₂))
    (hP : ∀ γ, arithmeticFundamentalGroupHom k κ f₂ x₂ (eP γ) =
      arithmeticFundamentalGroupHom k κ f₁ x₁ γ) :
    ∃ (t₁ : fiber x₁ ≅ fiber xi₁) (t₂ : fiber x₂ ≅ fiber xi₂),
      (∀ γ, arithmeticFundamentalGroupHom k κ f₁ xi₁
        (continuousConjAut t₁ γ) = arithmeticFundamentalGroupHom k κ f₁ x₁ γ) ∧
      (∀ γ, arithmeticFundamentalGroupHom k κ f₂ xi₂
        (continuousConjAut t₂ γ) = arithmeticFundamentalGroupHom k κ f₂ x₂ γ) ∧
      let α := (continuousConjAut t₁).symm.trans (eP.trans (continuousConjAut t₂))
      ∃ _hα : ∀ γ, arithmeticFundamentalGroupHom k κ f₂ xi₂ (α γ) =
          arithmeticFundamentalGroupHom k κ f₁ xi₁ γ,
      let _AkΩ₁ : Algebra k Ω₁ := (Spec.preimage (xi₁ ≫ f₁)).hom.toAlgebra
      let _AkΩ₂ : Algebra k Ω₂ := (Spec.preimage (xi₂ ≫ f₂)).hom.toAlgebra
      ∃ (b₁ : κ →ₐ[k] Ω₁) (b₂ : κ →ₐ[k] Ω₂),
      let _AκΩ₁ : Algebra κ Ω₁ := b₁.toRingHom.toAlgebra
      let _AκΩ₂ : Algebra κ Ω₂ := b₂.toRingHom.toAlgebra
      let _hkκΩ₁ : IsScalarTower k κ Ω₁ :=
        IsScalarTower.of_algebraMap_eq (fun a => (b₁.commutes a).symm)
      let _hkκΩ₂ : IsScalarTower k κ Ω₂ :=
        IsScalarTower.of_algebraMap_eq (fun a => (b₂.commutes a).symm)
      let hbase₁ : xi₁ ≫ f₁ = ξ k Ω₁ :=
        (Spec.map_preimage (xi₁ ≫ f₁)).symm
      let hbase₂ : xi₂ ≫ f₂ = ξ k Ω₂ :=
        (Spec.map_preimage (xi₂ ≫ f₂)).symm
      (fieldFiberExtensionIso k κ Ω₁ ≪≫ (eqToIso (congrArg fiber hbase₁)).symm =
        ((nonempty_fiber_iso (xi₁ ≫ f₁) (ξ k κ)).some).symm) ∧
      (fieldFiberExtensionIso k κ Ω₂ ≪≫ (eqToIso (congrArg fiber hbase₂)).symm =
        ((nonempty_fiber_iso (xi₂ ≫ f₂) (ξ k κ)).some).symm) := by
  obtain ⟨t₁, ht₁⟩ := exists_arithmetic_preserving_fiberIso
    k κ f₁ x₁ xi₁
  obtain ⟨t₂, ht₂⟩ := exists_arithmetic_preserving_fiberIso
    k κ f₂ x₂ xi₂
  refine ⟨t₁, t₂, ht₁, ht₂, ?_⟩
  intro α
  have hα : ∀ γ, arithmeticFundamentalGroupHom k κ f₂ xi₂ (α γ) =
      arithmeticFundamentalGroupHom k κ f₁ xi₁ γ := by
    intro γ
    change arithmeticFundamentalGroupHom k κ f₂ xi₂
      (continuousConjAut t₂ (eP ((continuousConjAut t₁).symm γ))) = _
    rw [ht₂, hP, ← ht₁, (continuousConjAut t₁).apply_symm_apply]
  refine ⟨hα, ?_⟩
  intro AkΩ₁ AkΩ₂
  obtain ⟨b₁, hb₁⟩ := exists_arithmeticAlignedCoefficientEmbedding
    k κ Ω₁ f₁ xi₁
  obtain ⟨b₂, hb₂⟩ := exists_arithmeticAlignedCoefficientEmbedding
    k κ Ω₂ f₂ xi₂
  refine ⟨b₁, b₂, ?_⟩
  intro AκΩ₁ AκΩ₂ hkκΩ₁ hkκΩ₂ hbase₁ hbase₂
  have halign₁ : fieldFiberExtensionIso k κ Ω₁ ≪≫
      (eqToIso (congrArg fiber hbase₁)).symm =
        ((nonempty_fiber_iso (xi₁ ≫ f₁) (ξ k κ)).some).symm := hb₁.1
  have halign₂ : fieldFiberExtensionIso k κ Ω₂ ≪≫
      (eqToIso (congrArg fiber hbase₂)).symm =
        ((nonempty_fiber_iso (xi₂ ≫ f₂) (ξ k κ)).some).symm := hb₂.1
  exact ⟨halign₁, halign₂⟩

/-- The actual finite rational models, ambient comparisons, inertia matching and
projective transformation retained for fixed aligned geometric points. -/
def genusZeroFiniteReconstructionResult
    (k : Type) [Field k] [NumberField k]
    {C₁ C₂ : Scheme}
    (c₁ : C₁ ⟶ Spec (.of k)) (c₂ : C₂ ⟶ Spec (.of k))
    [GeometricallyIntegral c₁]
    [GeometricallyIntegral c₂]
    (U₁ : C₁.Opens) (U₂ : C₂.Opens)
    (hU₁ : (U₁ : Set C₁).Nonempty) (hU₂ : (U₂ : Set C₂).Nonempty) :
    let κ := AlgebraicClosure k
    let _hC₁ : IsIntegral C₁ := GeometricallyIntegral.isIntegral_of_subsingleton c₁
    let _hC₂ : IsIntegral C₂ := GeometricallyIntegral.isIntegral_of_subsingleton c₂
    let _hN₁ : Nonempty (U₁ : Scheme) := ⟨⟨hU₁.choose, hU₁.choose_spec⟩⟩
    let _hN₂ : Nonempty (U₂ : Scheme) := ⟨⟨hU₂.choose, hU₂.choose_spec⟩⟩
    let _hI₁ : IsIntegral (U₁ : Scheme) := isIntegral_of_isOpenImmersion U₁.ι
    let _hI₂ : IsIntegral (U₂ : Scheme) := isIntegral_of_isOpenImmersion U₂.ι
    let Ω₁ := AlgebraicClosure (U₁ : Scheme).functionField
    let Ω₂ := AlgebraicClosure (U₂ : Scheme).functionField
    let xi₁ := (U₁ : Scheme).genericExtensionMorphism Ω₁
    let xi₂ := (U₂ : Scheme).genericExtensionMorphism Ω₂
    ∀ (α : π₁ᵉᵗ(xi₁) ≃ₜ* π₁ᵉᵗ(xi₂))
      (_hα : ∀ γ, arithmeticFundamentalGroupHom k κ (U₂.ι ≫ c₂) xi₂ (α γ) =
        arithmeticFundamentalGroupHom k κ (U₁.ι ≫ c₁) xi₁ γ),
      let _AkΩ₁ : Algebra k Ω₁ := (Spec.preimage (xi₁ ≫ (U₁.ι ≫ c₁))).hom.toAlgebra
      let _AkΩ₂ : Algebra k Ω₂ := (Spec.preimage (xi₂ ≫ (U₂.ι ≫ c₂))).hom.toAlgebra
      ∀ (_b₁ : κ →ₐ[k] Ω₁) (_b₂ : κ →ₐ[k] Ω₂),
      Prop := by
  intro κ hC₁ hC₂ hN₁ hN₂ hI₁ hI₂ Ω₁ Ω₂ xi₁ xi₂ α hα AkΩ₁ AkΩ₂ b₁ b₂
  exact
      let _AκΩ₁ : Algebra κ Ω₁ := b₁.toRingHom.toAlgebra
      let _AκΩ₂ : Algebra κ Ω₂ := b₂.toRingHom.toAlgebra
      let _hkκΩ₁ : IsScalarTower k κ Ω₁ :=
        IsScalarTower.of_algebraMap_eq (fun a => (b₁.commutes a).symm)
      let _hkκΩ₂ : IsScalarTower k κ Ω₂ :=
        IsScalarTower.of_algebraMap_eq (fun a => (b₂.commutes a).symm)
      ∃ E : FiniteGaloisIntermediateField k κ,
      let _hE : NumberField E := NumberField.of_module_finite k E
      let _hEκ : IsAlgClosure E κ :=
        ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := k) (L := E) (A := κ)⟩
      let _hFE : IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
        constantField_specMap_isFiniteEtale k E
      ∃ s t : Finset (Projectivization E (E × E)),
        3 ≤ s.card ∧ 3 ≤ t.card ∧
      ∃ (I₁ : pullback c₁ (specMap k E) ≅ (projectiveLineRatFuncModel E).C)
        (I₂ : pullback c₂ (specMap k E) ≅ (projectiveLineRatFuncModel E).C),
        I₁.hom ≫ (projectiveLineRatFuncModel E).toBase = pullback.snd c₁ (specMap k E) ∧
        I₂.hom ≫ (projectiveLineRatFuncModel E).toBase = pullback.snd c₂ (specMap k E) ∧
      ∃ (Js : pullback (specMap k E) (U₁.ι ≫ c₁) ≅ (rationalConfigurationOpen s : Scheme))
        (Jt : pullback (specMap k E) (U₂.ι ≫ c₂) ≅ (rationalConfigurationOpen t : Scheme)),
      ∃ (hJs : Js.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
          pullback.fst (specMap k E) (U₁.ι ≫ c₁))
        (hJt : Jt.hom ≫ ((rationalConfigurationOpen t).ι ≫ π E 1) =
          pullback.fst (specMap k E) (U₂.ι ≫ c₂)),
        (Js.hom ≫ (rationalConfigurationOpen s).ι =
          (openBaseChangeIso c₁ (specMap k E) U₁).hom ≫
            (pullback.fst c₁ (specMap k E) ⁻¹ᵁ U₁).ι ≫ I₁.hom) ∧
        (Jt.hom ≫ (rationalConfigurationOpen t).ι =
          (openBaseChangeIso c₂ (specMap k E) U₂).hom ≫
            (pullback.fst c₂ (specMap k E) ⁻¹ᵁ U₂).ι ≫ I₂.hom) ∧
      let Ys := pullback (specMap E κ) (pullback.fst (specMap k E) (U₁.ι ≫ c₁))
      let Yt := pullback (specMap E κ) (pullback.fst (specMap k E) (U₂.ι ≫ c₂))
      let Zs := rationalConfigurationGeometricScheme E κ s
      let Zt := rationalConfigurationGeometricScheme E κ t
      let Jκs := rationalModelGeometricIso k E κ (U₁.ι ≫ c₁) s Js hJs
      let Jκt := rationalModelGeometricIso k E κ (U₂.ι ≫ c₂) t Jt hJt
      ∃ (_hYs : IsIntegral Ys) (_hYt : IsIntegral Yt),
      ∃ (aS : Ys.functionField →+* Ω₁) (aT : Yt.functionField →+* Ω₂),
      let _AYs : Algebra Ys.functionField Ω₁ := aS.toAlgebra
      let _AYt : Algebra Yt.functionField Ω₂ := aT.toAlgebra;
        IsAlgClosure Ys.functionField Ω₁ ∧ IsAlgClosure Yt.functionField Ω₂ ∧
      let _AZs : Algebra Zs.functionField Ω₁ := namedBaseTransportAmbientAlgebra Jκs Ω₁
      let _AZt : Algebra Zt.functionField Ω₂ := namedBaseTransportAmbientAlgebra Jκt Ω₂
      ∃ (_hZs : @IsAlgClosure Zs.functionField Ω₁ _ _ _
          DivisionSemiring.to_moduleIsTorsionFree)
        (_hZt : @IsAlgClosure Zt.functionField Ω₂ _ _ _
          DivisionSemiring.to_moduleIsTorsionFree),
        (Ys.genericExtensionMorphism Ω₁ ≫ Jκs.hom = Zs.genericExtensionMorphism Ω₁) ∧
        (Yt.genericExtensionMorphism Ω₂ ≫ Jκt.hom = Zt.genericExtensionMorphism Ω₂) ∧
        (Zs.genericExtensionMorphism Ω₁ ≫ pullback.fst (specMap E κ)
          ((rationalConfigurationOpen s).ι ≫ π E 1) = ξ κ Ω₁) ∧
        (Zt.genericExtensionMorphism Ω₂ ≫ pullback.fst (specMap E κ)
          ((rationalConfigurationOpen t).ι ≫ π E 1) = ξ κ Ω₂) ∧
      ∃ (hxs : arithmeticConstantFieldLift k E κ (U₁.ι ≫ c₁) xi₁ ≫ Js.hom =
          rationalConfigurationArithmeticBasePoint E κ s Ω₁)
        (hxt : arithmeticConstantFieldLift k E κ (U₂.ι ≫ c₂) xi₂ ≫ Jt.hom =
          rationalConfigurationArithmeticBasePoint E κ t Ω₂),
      let xsE := arithmeticConstantFieldLift k E κ (U₁.ι ≫ c₁) xi₁
      let xtE := arithmeticConstantFieldLift k E κ (U₂.ι ≫ c₂) xi₂
      let xs := rationalConfigurationArithmeticBasePoint E κ s Ω₁
      let xt := rationalConfigurationArithmeticBasePoint E κ t Ω₂
      let _hconnS : ConnectedSpace (pullback (specMap k E) (U₁.ι ≫ c₁) : Scheme) :=
        Js.hom.homeomorph.connectedSpace_iff.mpr inferInstance
      let _hconnT : ConnectedSpace (pullback (specMap k E) (U₂.ι ≫ c₂) : Scheme) :=
        Jt.hom.homeomorph.connectedSpace_iff.mpr inferInstance
      let es := namedModelPointedGroupEquiv Js xsE xs hxs
      let et := namedModelPointedGroupEquiv Jt xtE xt hxt
      ∃ d : π₁ᵉᵗ(xtE),
        arithmeticFundamentalGroupHom E κ
            (pullback.fst (specMap k E) (U₂.ι ≫ c₂)) xtE d =
          (arithmeticConstantFieldComparisonOverE k E κ (U₂.ι ≫ c₂) xi₂ *
            (arithmeticConstantFieldComparisonOverE k E κ (U₁.ι ≫ c₁) xi₁)⁻¹)⁻¹ ∧
      let β := es.symm.trans
        ((ProCGroups.innerCorrectedGroupEquiv
          (arithmeticConstantFieldCoverGroupTransport k E κ (U₁.ι ≫ c₁) (U₂.ι ≫ c₂)
            xi₁ xi₂ α hα) d).trans et)
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
      ∃ I : (rationalConfigurationOpen s : Scheme) ≅ (rationalConfigurationOpen t : Scheme),
        I.hom ≫ (rationalConfigurationOpen t).ι =
          (rationalConfigurationOpen s).ι ≫ (pairLinearCoordinateIso f).hom ∧
        I.hom ≫ ((rationalConfigurationOpen t).ι ≫ π E 1) =
          (rationalConfigurationOpen s).ι ≫ π E 1

private theorem exists_reconstruction_of_aligned_fibers
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
    let κ := AlgebraicClosure k
    let _hC₁ : IsIntegral C₁ := GeometricallyIntegral.isIntegral_of_subsingleton c₁
    let _hC₂ : IsIntegral C₂ := GeometricallyIntegral.isIntegral_of_subsingleton c₂
    let _hN₁ : Nonempty (U₁ : Scheme) := ⟨⟨hU₁.choose, hU₁.choose_spec⟩⟩
    let _hN₂ : Nonempty (U₂ : Scheme) := ⟨⟨hU₂.choose, hU₂.choose_spec⟩⟩
    let _hI₁ : IsIntegral (U₁ : Scheme) := isIntegral_of_isOpenImmersion U₁.ι
    let _hI₂ : IsIntegral (U₂ : Scheme) := isIntegral_of_isOpenImmersion U₂.ι
    let Ω₁ := AlgebraicClosure (U₁ : Scheme).functionField
    let Ω₂ := AlgebraicClosure (U₂ : Scheme).functionField
    let xi₁ := (U₁ : Scheme).genericExtensionMorphism Ω₁
    let xi₂ := (U₂ : Scheme).genericExtensionMorphism Ω₂
    ∀ (α : π₁ᵉᵗ(xi₁) ≃ₜ* π₁ᵉᵗ(xi₂))
      (hα : ∀ γ, arithmeticFundamentalGroupHom k κ (U₂.ι ≫ c₂) xi₂ (α γ) =
        arithmeticFundamentalGroupHom k κ (U₁.ι ≫ c₁) xi₁ γ),
      let _AkΩ₁ : Algebra k Ω₁ := (Spec.preimage (xi₁ ≫ (U₁.ι ≫ c₁))).hom.toAlgebra
      let _AkΩ₂ : Algebra k Ω₂ := (Spec.preimage (xi₂ ≫ (U₂.ι ≫ c₂))).hom.toAlgebra
      ∀ (b₁ : κ →ₐ[k] Ω₁) (b₂ : κ →ₐ[k] Ω₂),
      let _AκΩ₁ : Algebra κ Ω₁ := b₁.toRingHom.toAlgebra
      let _AκΩ₂ : Algebra κ Ω₂ := b₂.toRingHom.toAlgebra
      let _hkκΩ₁ : IsScalarTower k κ Ω₁ :=
        IsScalarTower.of_algebraMap_eq (fun a => (b₁.commutes a).symm)
      let _hkκΩ₂ : IsScalarTower k κ Ω₂ :=
        IsScalarTower.of_algebraMap_eq (fun a => (b₂.commutes a).symm)
      let hbase₁ : xi₁ ≫ (U₁.ι ≫ c₁) = ξ k Ω₁ :=
        (Spec.map_preimage (xi₁ ≫ (U₁.ι ≫ c₁))).symm
      let hbase₂ : xi₂ ≫ (U₂.ι ≫ c₂) = ξ k Ω₂ :=
        (Spec.map_preimage (xi₂ ≫ (U₂.ι ≫ c₂))).symm
      ∀ (_halign₁ : fieldFiberExtensionIso k κ Ω₁ ≪≫
          (eqToIso (congrArg fiber hbase₁)).symm =
            ((nonempty_fiber_iso (xi₁ ≫ (U₁.ι ≫ c₁)) (ξ k κ)).some).symm)
        (_halign₂ : fieldFiberExtensionIso k κ Ω₂ ≪≫
          (eqToIso (congrArg fiber hbase₂)).symm =
            ((nonempty_fiber_iso (xi₂ ≫ (U₂.ι ≫ c₂)) (ξ k κ)).some).symm),
      genusZeroFiniteReconstructionResult k c₁ c₂ U₁ U₂ hU₁ hU₂ α hα b₁ b₂ := by
  intro κ hC₁ hC₂ hN₁ hN₂ hI₁ hI₂ Ω₁ Ω₂ xi₁ xi₂ α hα
    AkΩ₁ AkΩ₂ b₁ b₂ AκΩ₁ AκΩ₂ hkκΩ₁ hkκΩ₂ hbase₁ hbase₂ halign₁ halign₂
  have : Surjective (U₁.ι ≫ c₁) :=
    ⟨fun y => ⟨Nonempty.some inferInstance, Subsingleton.elim _ y⟩⟩
  have : Surjective (U₂.ι ≫ c₂) :=
    ⟨fun y => ⟨Nonempty.some inferInstance, Subsingleton.elim _ y⟩⟩
  have : GeometricallyIntegral (U₁.ι ≫ c₁) :=
    GeometricallyIntegral.comp_of_isOpenImmersion U₁.ι c₁
  have : GeometricallyIntegral (U₂.ι ≫ c₂) :=
    GeometricallyIntegral.comp_of_isOpenImmersion U₂.ι c₂
  have : GeometricallyConnected (U₁.ι ≫ c₁) :=
    GeometricallyIrreducible.geometricallyConnected (U₁.ι ≫ c₁)
  have : GeometricallyConnected (U₂.ι ≫ c₂) :=
    GeometricallyIrreducible.geometricallyConnected (U₂.ι ≫ c₂)
  obtain ⟨E, s, t, hs, ht, I₁, I₂, hproper₁, hproper₂,
      Js, Jt, hJs, hJt, hJsambient, hJtambient⟩ :=
    exists_common_rational_models_of_geometricGenus_zero
      k c₁ c₂ U₁ U₂ hU₁ hU₂ hg₁ hg₂ hr₁ hr₂
  refine ⟨E, ?_⟩
  intro hE hEκ hFE
  refine ⟨s, t, hs, ht, I₁, I₂, hproper₁, hproper₂,
    Js, Jt, hJs, hJt, hJsambient, hJtambient, ?_⟩
  intro Ys Yt Zs Zt Jκs Jκt
  have : IsIntegral (pullback (specMap k E) (U₁.ι ≫ c₁)) :=
    IsIntegral.of_isIso (pullbackSymmetry (U₁.ι ≫ c₁) (specMap k E)).hom
  have : IsIntegral (pullback (specMap k E) (U₂.ι ≫ c₂)) :=
    IsIntegral.of_isIso (pullbackSymmetry (U₂.ι ≫ c₂) (specMap k E)).hom
  have : GeometricallyIntegral (pullback.fst (specMap k E) (U₁.ι ≫ c₁)) :=
    MorphismProperty.of_isPullback (P := (show MorphismProperty Scheme from @GeometricallyIntegral))
      (IsPullback.of_hasPullback (specMap k E) (U₁.ι ≫ c₁)).flip inferInstance
  have : GeometricallyIntegral (pullback.fst (specMap k E) (U₂.ι ≫ c₂)) :=
    MorphismProperty.of_isPullback (P := (show MorphismProperty Scheme from @GeometricallyIntegral))
      (IsPullback.of_hasPullback (specMap k E) (U₂.ι ≫ c₂)).flip inferInstance
  have hYs : IsIntegral Ys := IsIntegral.of_isIso
    (pullbackSymmetry (pullback.fst (specMap k E) (U₁.ι ≫ c₁)) (specMap E κ)).hom
  have hYt : IsIntegral Yt := IsIntegral.of_isIso
    (pullbackSymmetry (pullback.fst (specMap k E) (U₂.ι ≫ c₂)) (specMap E κ)).hom
  obtain ⟨aS, haS⟩ := exists_alignedRationalModel_genericAmbient
    k E κ Ω₁ (U₁.ι ≫ c₁) hbase₁ halign₁ s Js hJs
  obtain ⟨aT, haT⟩ := exists_alignedRationalModel_genericAmbient
    k E κ Ω₂ (U₂.ι ≫ c₂) hbase₂ halign₂ t Jt hJt
  refine ⟨hYs, hYt, aS, aT, ?_⟩
  intro AYs AYt
  obtain ⟨hAS, hZS⟩ := haS
  obtain ⟨hAT, hZT⟩ := haT
  refine ⟨hAS, hAT, ?_⟩
  intro AZs AZt
  obtain ⟨hclosureS, hpointS, hcoefS, hxs⟩ := hZS
  obtain ⟨hclosureT, hpointT, hcoefT, hxt⟩ := hZT
  refine ⟨hclosureS, hclosureT, hpointS, hpointT, hcoefS, hcoefT, hxs.symm, hxt.symm, ?_⟩
  exact exists_projectiveTransformation_of_pointed_constantCover_models
    k E κ (U₁.ι ≫ c₁) (U₂.ι ≫ c₂) xi₁ xi₂ s t hs ht
    Js Jt hJs hJt hxs.symm hxt.symm α hα

/-- Construct the aligned finite reconstruction and retain its actual witnesses.
The only curve data supplied are the compactifications, nonempty opens, genus
zero, at least three geometric punctures, and the original arithmetic isomorphism. -/
theorem exists_genusZero_finite_reconstruction
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
        x.val ∉ pullback.fst c₂ (specMap k (AlgebraicClosure k)) ⁻¹ᵁ U₂})
    {Λ₁ Λ₂ : Type} [Field Λ₁] [Field Λ₂] [IsSepClosed Λ₁] [IsSepClosed Λ₂]
    (x₁ : Spec (.of Λ₁) ⟶ (U₁ : Scheme)) (x₂ : Spec (.of Λ₂) ⟶ (U₂ : Scheme))
    (eP : π₁ᵉᵗ(x₁) ≃ₜ* π₁ᵉᵗ(x₂))
    (hP : ∀ γ, arithmeticFundamentalGroupHom k (AlgebraicClosure k)
        (U₂.ι ≫ c₂) x₂ (eP γ) =
      arithmeticFundamentalGroupHom k (AlgebraicClosure k) (U₁.ι ≫ c₁) x₁ γ) :
    let κ := AlgebraicClosure k
    let _hC₁ : IsIntegral C₁ := GeometricallyIntegral.isIntegral_of_subsingleton c₁
    let _hC₂ : IsIntegral C₂ := GeometricallyIntegral.isIntegral_of_subsingleton c₂
    let _hN₁ : Nonempty (U₁ : Scheme) := ⟨⟨hU₁.choose, hU₁.choose_spec⟩⟩
    let _hN₂ : Nonempty (U₂ : Scheme) := ⟨⟨hU₂.choose, hU₂.choose_spec⟩⟩
    let _hI₁ : IsIntegral (U₁ : Scheme) := isIntegral_of_isOpenImmersion U₁.ι
    let _hI₂ : IsIntegral (U₂ : Scheme) := isIntegral_of_isOpenImmersion U₂.ι
    let Ω₁ := AlgebraicClosure (U₁ : Scheme).functionField
    let Ω₂ := AlgebraicClosure (U₂ : Scheme).functionField
    let xi₁ := (U₁ : Scheme).genericExtensionMorphism Ω₁
    let xi₂ := (U₂ : Scheme).genericExtensionMorphism Ω₂
    ∃ (t₁ : fiber x₁ ≅ fiber xi₁) (t₂ : fiber x₂ ≅ fiber xi₂),
      (∀ γ, arithmeticFundamentalGroupHom k κ (U₁.ι ≫ c₁) xi₁
        (continuousConjAut t₁ γ) = arithmeticFundamentalGroupHom k κ (U₁.ι ≫ c₁) x₁ γ) ∧
      (∀ γ, arithmeticFundamentalGroupHom k κ (U₂.ι ≫ c₂) xi₂
        (continuousConjAut t₂ γ) = arithmeticFundamentalGroupHom k κ (U₂.ι ≫ c₂) x₂ γ) ∧
      let α := (continuousConjAut t₁).symm.trans (eP.trans (continuousConjAut t₂))
      ∃ hα : ∀ γ, arithmeticFundamentalGroupHom k κ (U₂.ι ≫ c₂) xi₂ (α γ) =
          arithmeticFundamentalGroupHom k κ (U₁.ι ≫ c₁) xi₁ γ,
      let _AkΩ₁ : Algebra k Ω₁ := (Spec.preimage (xi₁ ≫ (U₁.ι ≫ c₁))).hom.toAlgebra
      let _AkΩ₂ : Algebra k Ω₂ := (Spec.preimage (xi₂ ≫ (U₂.ι ≫ c₂))).hom.toAlgebra
      ∃ (b₁ : κ →ₐ[k] Ω₁) (b₂ : κ →ₐ[k] Ω₂),
      let _AκΩ₁ : Algebra κ Ω₁ := b₁.toRingHom.toAlgebra
      let _AκΩ₂ : Algebra κ Ω₂ := b₂.toRingHom.toAlgebra
      let _hkκΩ₁ : IsScalarTower k κ Ω₁ :=
        IsScalarTower.of_algebraMap_eq (fun a => (b₁.commutes a).symm)
      let _hkκΩ₂ : IsScalarTower k κ Ω₂ :=
        IsScalarTower.of_algebraMap_eq (fun a => (b₂.commutes a).symm)
      let hbase₁ : xi₁ ≫ (U₁.ι ≫ c₁) = ξ k Ω₁ :=
        (Spec.map_preimage (xi₁ ≫ (U₁.ι ≫ c₁))).symm
      let hbase₂ : xi₂ ≫ (U₂.ι ≫ c₂) = ξ k Ω₂ :=
        (Spec.map_preimage (xi₂ ≫ (U₂.ι ≫ c₂))).symm
      (fieldFiberExtensionIso k κ Ω₁ ≪≫ (eqToIso (congrArg fiber hbase₁)).symm =
        ((nonempty_fiber_iso (xi₁ ≫ (U₁.ι ≫ c₁)) (ξ k κ)).some).symm) ∧
      (fieldFiberExtensionIso k κ Ω₂ ≪≫ (eqToIso (congrArg fiber hbase₂)).symm =
        ((nonempty_fiber_iso (xi₂ ≫ (U₂.ι ≫ c₂)) (ξ k κ)).some).symm) ∧
      genusZeroFiniteReconstructionResult k c₁ c₂ U₁ U₂ hU₁ hU₂ α hα b₁ b₂ := by
  intro κ hC₁ hC₂ hN₁ hN₂ hI₁ hI₂ Ω₁ Ω₂ xi₁ xi₂
  have : Surjective (U₁.ι ≫ c₁) :=
    ⟨fun y => ⟨Nonempty.some inferInstance, Subsingleton.elim _ y⟩⟩
  have : Surjective (U₂.ι ≫ c₂) :=
    ⟨fun y => ⟨Nonempty.some inferInstance, Subsingleton.elim _ y⟩⟩
  have : GeometricallyIntegral (U₁.ι ≫ c₁) :=
    GeometricallyIntegral.comp_of_isOpenImmersion U₁.ι c₁
  have : GeometricallyIntegral (U₂.ι ≫ c₂) :=
    GeometricallyIntegral.comp_of_isOpenImmersion U₂.ι c₂
  have : GeometricallyConnected (U₁.ι ≫ c₁) :=
    GeometricallyIrreducible.geometricallyConnected (U₁.ι ≫ c₁)
  have : GeometricallyConnected (U₂.ι ≫ c₂) :=
    GeometricallyIrreducible.geometricallyConnected (U₂.ι ≫ c₂)
  obtain ⟨t₁, t₂, ht₁, ht₂, h⟩ :=
    exists_aligned_fiber_comparisons k κ Ω₁ Ω₂ (U₁.ι ≫ c₁) (U₂.ι ≫ c₂)
      x₁ x₂ xi₁ xi₂ eP hP
  refine ⟨t₁, t₂, ht₁, ht₂, ?_⟩
  intro α
  obtain ⟨hα, h⟩ := h
  refine ⟨hα, ?_⟩
  intro AkΩ₁ AkΩ₂
  obtain ⟨b₁, b₂, h⟩ := h
  refine ⟨b₁, b₂, ?_⟩
  intro AκΩ₁ AκΩ₂ hkκΩ₁ hkκΩ₂ hbase₁ hbase₂
  obtain ⟨halign₁, halign₂⟩ := h
  refine ⟨halign₁, halign₂, ?_⟩
  exact exists_reconstruction_of_aligned_fibers k c₁ c₂ U₁ U₂ hU₁ hU₂
    hg₁ hg₂ hr₁ hr₂ α hα b₁ b₂ halign₁ halign₂

end AnabelianGeometry.WeightFiltration
