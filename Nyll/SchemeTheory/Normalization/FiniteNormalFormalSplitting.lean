/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Normalization.GenericFiber.GenericExtension
public import Nyll.SchemeTheory.Normalization.FiniteNormalSource
public import Nyll.SchemeTheory.RingTheory.Henselian.FormalSeparableTensorSplitting
public import Mathlib.AlgebraicGeometry.Limits

/-! # The labelled formal generic fibre of a finite normal morphism

The finite normal source is its actual generic relative normalization.
Consequently its generic-fibre square is cartesian. Base change through a
power-series deformation then produces the coproduct of the formal lifts
of the residue field embeddings, with both projections computed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Hom

/-- The generic fibre of a finite morphism with normal integral source is
its actual function field. The given field algebra is tied to the map by
the original generic-point commutative square. -/
theorem isPullback_finiteNormal_generic
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNormalIntegral Y]
    (f : Y ⟶ X) [IsFinite f]
    [Algebra X.functionField Y.functionField]
    [Algebra.IsAlgebraic X.functionField Y.functionField]
    (hgeneric : Y.fromSpecStalk (genericPoint Y) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField Y.functionField)) ≫
        X.fromSpecStalk (genericPoint X)) :
    IsPullback (Y.fromSpecStalk (genericPoint Y))
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Y.functionField)))
      f (X.fromSpecStalk (genericPoint X)) := by
  have hy : Y.genericExtensionMorphism Y.functionField =
      Y.fromSpecStalk (genericPoint Y) := by
    change Spec.map (𝟙 (CommRingCat.of Y.functionField)) ≫ _ = _
    rw [Spec.map_id, Category.id_comp]
  have hgen : Y.genericExtensionMorphism Y.functionField ≫ f =
      X.genericExtensionMorphism Y.functionField := by
    rw [hy]
    exact hgeneric
  have h := EtaleFundamentalGroups.isPullback_genericExtensionNormalization
    X Y.functionField
  rw [← hgen] at h
  have h' : IsPullback (Y.genericExtensionMorphism Y.functionField)
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Y.functionField)))
      f (X.fromSpecStalk (genericPoint X)) := by
    apply h.of_iso (Iso.refl _) (finiteNormalGenericIso f) (Iso.refl _) (Iso.refl _)
    · simpa only [Iso.refl_hom, Category.id_comp] using
        toNormalization_finiteNormalGenericIso_hom f
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · simp only [Iso.refl_hom, Category.comp_id]
      calc
        _ = (finiteNormalGenericIso f).hom ≫
            (finiteNormalGenericIso f).inv ≫
              (Y.genericExtensionMorphism Y.functionField ≫ f).fromNormalization :=
          ((finiteNormalGenericIso f).hom_inv_id_assoc _).symm
        _ = _ := congrArg (fun a => (finiteNormalGenericIso f).hom ≫ a)
          (finiteNormalGenericIso_inv_fromNormalization f)
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  rw [← hy]
  exact h'

/-- A power-series deformation of the base function field splits the
actual base-changed finite normal scheme. Its labelled components are the
constructed formal lifts, not an unlabelled isomorphism of finite schemes. -/
theorem exists_formalGenericFibre_coprod_iso
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNormalIntegral Y]
    (f : Y ⟶ X) [IsFinite f]
    [Algebra X.functionField Y.functionField]
    [FiniteDimensional X.functionField Y.functionField]
    [Algebra.IsSeparable X.functionField Y.functionField]
    (hgeneric : Y.fromSpecStalk (genericPoint Y) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField Y.functionField)) ≫
        X.fromSpecStalk (genericPoint X))
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω] [IsAlgClosed Ω]
    (τ : X.functionField →+* PowerSeries Ω)
    (hτ : PowerSeries.constantCoeff.comp τ = algebraMap X.functionField Ω) :
    ∃ e : (∐ fun _ : Y.functionField →ₐ[X.functionField] Ω =>
        Spec (CommRingCat.of (PowerSeries Ω))) ≅
      pullback f (Spec.map (CommRingCat.ofHom τ) ≫ X.fromSpecStalk (genericPoint X)),
      e.hom ≫ pullback.snd f
          (Spec.map (CommRingCat.ofHom τ) ≫ X.fromSpecStalk (genericPoint X)) =
        Sigma.desc (fun _ : Y.functionField →ₐ[X.functionField] Ω =>
          𝟙 (Spec (CommRingCat.of (PowerSeries Ω)))) ∧
      ∀ ι : Y.functionField →ₐ[X.functionField] Ω,
        Sigma.ι (fun _ : Y.functionField →ₐ[X.functionField] Ω =>
            Spec (CommRingCat.of (PowerSeries Ω))) ι ≫
          e.hom ≫ pullback.fst f
            (Spec.map (CommRingCat.ofHom τ) ≫ X.fromSpecStalk (genericPoint X)) =
          Spec.map (CommRingCat.ofHom (PowerSeries.formalEmbeddingLift τ hτ ι)) ≫
            Y.fromSpecStalk (genericPoint Y) := by
  classical
  let E := X.functionField
  let F := Y.functionField
  let R := PowerSeries Ω
  let algR : Algebra E R := τ.toAlgebra
  let _ : Module E R := algR.toModule
  let _ : Fintype (F →ₐ[E] Ω) :=
    PowerBasis.AlgHom.fintype (Field.powerBasisOfFiniteOfSeparable E F)
  obtain ⟨eAlg, heAlg⟩ := PowerSeries.exists_formalTensorProductEquiv (F := F) τ hτ
  let eSpec : Spec (CommRingCat.of ((F →ₐ[E] Ω) → R)) ≅
      Spec (CommRingCat.of (R ⊗[E] F)) :=
    Scheme.Spec.mapIso eAlg.toRingEquiv.toCommRingCatIso.op
  let d : (∐ fun _ : F →ₐ[E] Ω => Spec (CommRingCat.of R)) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap E F)))
        (Spec.map (CommRingCat.ofHom τ)) :=
    asIso (sigmaSpec (fun _ : F →ₐ[E] Ω => CommRingCat.of R)) ≪≫ eSpec ≪≫
      (pullbackSpecIso E R F).symm ≪≫ pullbackSymmetry _ _
  have heBase : eSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[E] F))) =
      Spec.map (CommRingCat.ofHom (algebraMap R ((F →ₐ[E] Ω) → R))) := by
    change Spec.map (CommRingCat.ofHom eAlg.toRingHom) ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext eAlg.commutes)
  have hdBase : d.hom ≫ pullback.snd _ _ =
      Sigma.desc (fun _ : F →ₐ[E] Ω => 𝟙 (Spec (CommRingCat.of R))) := by
    simp only [d, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
      pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst']
    rw [heBase]
    apply Sigma.hom_ext
    intro ι
    rw [ι_sigmaSpec_assoc, Sigma.ι_comp_desc, ← Spec.map_comp]
    exact Spec.map_id _
  have hdComponent (ι : F →ₐ[E] Ω) :
      Sigma.ι (fun _ : F →ₐ[E] Ω => Spec (CommRingCat.of R)) ι ≫
        d.hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (PowerSeries.formalEmbeddingLift τ hτ ι)) := by
    simp only [d, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
      pullbackSymmetry_hom_comp_fst, pullbackSpecIso_inv_snd, ι_sigmaSpec_assoc]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ ι)) ≫
      Spec.map (CommRingCat.ofHom eAlg.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom)) = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change eAlg ((1 : R) ⊗ₜ[E] a) ι = PowerSeries.formalEmbeddingLift τ hτ ι a
    rw [heAlg, one_mul]
  have hNative := isPullback_finiteNormal_generic f hgeneric
  have hSquare := (IsPullback.of_hasPullback
    (Spec.map (CommRingCat.ofHom (algebraMap E F)))
    (Spec.map (CommRingCat.ofHom τ))).paste_horiz hNative
  refine ⟨d ≪≫ hSquare.isoPullback, ?_, ?_⟩
  · simp only [Iso.trans_hom, Category.assoc, hSquare.isoPullback_hom_snd]
    exact hdBase
  · intro ι
    simp only [Iso.trans_hom, Category.assoc, hSquare.isoPullback_hom_fst]
    simpa only [Category.assoc] using
      congrArg (fun g => g ≫ Y.fromSpecStalk (genericPoint Y)) (hdComponent ι)

end AlgebraicGeometry.Scheme.Hom
