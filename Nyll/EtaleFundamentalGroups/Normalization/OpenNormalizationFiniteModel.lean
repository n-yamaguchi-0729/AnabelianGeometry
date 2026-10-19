/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Normalization.FiniteNormalFieldSourceGeneric
import Mathlib.AlgebraicGeometry.Normalization

/-! # The same open normalization inside its actual finite normal model

Smooth base change of relative normalization identifies the original open
normalization with the literal inverse image of the original open in a finite
normal model. The comparison retains the generic source, as well as projection.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace EtaleFundamentalGroups

private def factorThroughMonoPullbackIso
    {A U C : Scheme} (g : A ⟶ U) (j : U ⟶ C) [Mono j] :
    A ≅ pullback (g ≫ j) j where
  hom := pullback.lift (𝟙 A) g (Category.id_comp _)
  inv := pullback.fst (g ≫ j) j
  hom_inv_id := pullback.lift_fst _ _ _
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · apply (cancel_mono j).mp
      simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
      exact pullback.condition

/-- Restrict an actual normalization model along an open immersion. The same
normalization map, rather than an abstract field or cover, is identified. -/
theorem exists_openNormalization_iso_pullback_of_model
    {A U C N : Scheme} (g : A ⟶ U)
    [QuasiCompact g] [QuasiSeparated g]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (d : N ⟶ C) (e : (g ≫ j).normalization ≅ N)
    (he : e.hom ≫ d = (g ≫ j).fromNormalization) :
    ∃ E : g.normalization ≅ pullback d j,
      E.hom ≫ pullback.snd d j = g.fromNormalization ∧
      g.toNormalization ≫ E.hom ≫ pullback.fst d j =
        (g ≫ j).toNormalization ≫ e.hom := by
  let eSource := factorThroughMonoPullbackIso g j
  have hSource : eSource.hom ≫ pullback.snd (g ≫ j) j = g := by
    simp only [eSource, factorThroughMonoPullbackIso, pullback.lift_snd]
  let eNorm := Inertia.normalizationSourceIso g (pullback.snd (g ≫ j) j) eSource hSource
  let eBase := asIso ((g ≫ j).normalizationPullback j)
  let eModel := asIso (pullback.map (g ≫ j).fromNormalization j d j
    e.hom (𝟙 U) (𝟙 C) (by simpa only [Category.comp_id] using he.symm)
    (by rw [Category.comp_id, Category.id_comp]))
  refine ⟨eNorm ≪≫ eBase ≪≫ eModel, ?_, ?_⟩
  · simp only [Iso.trans_hom, Category.assoc, eModel, asIso_hom,
      pullback.lift_snd, Category.comp_id, eBase,
      Scheme.Hom.normalizationPullback_snd, eNorm,
      Inertia.normalizationSourceIso_hom_fromNormalization]
  · simp only [Iso.trans_hom, Category.assoc, eModel, asIso_hom,
      pullback.lift_fst, eBase, eNorm,
      Inertia.toNormalization_normalizationSourceIso_hom_assoc,
      Scheme.Hom.toNormalization_normalizationPullback_fst_assoc,
      eSource, factorThroughMonoPullbackIso, pullback.lift_fst_assoc, Category.id_comp]

/-- A specified generic field source of the same finite normal model identifies
its original open normalization with the actual inverse-image open. -/
theorem exists_openNormalization_iso_pullback_of_generic_field
    {U C N : Scheme} [IsIntegral N] [IsNormalIntegral N]
    {L : Type} [Field L] (g : Spec (.of L) ⟶ U)
    [QuasiCompact g] [QuasiSeparated g]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (d : N ⟶ C) [IsFinite d] (q : Spec (.of L) ⟶ N)
    [IsDominant q] [IsPreimmersion q] [QuasiCompact q] [QuasiSeparated q]
    (h : q ≫ d = g ≫ j) :
    ∃ E : g.normalization ≅ pullback d j,
      E.hom ≫ pullback.snd d j = g.fromNormalization ∧
      g.toNormalization ≫ E.hom ≫ pullback.fst d j = q := by
  let eSource := Inertia.normalizationSourceIso (g ≫ j) (q ≫ d) (Iso.refl _)
    (by simpa only [Iso.refl_hom, Category.id_comp] using h)
  let eModel := finiteNormalFieldSourceIso d q
  have hModel : (eSource ≪≫ eModel).hom ≫ d = (g ≫ j).fromNormalization := by
    rw [Iso.trans_hom, Category.assoc, finiteNormalFieldSourceIso_hom_fromNormalization]
    exact Inertia.normalizationSourceIso_hom_fromNormalization _ _ _ _
  obtain ⟨E, hE, hgeneric⟩ :=
    exists_openNormalization_iso_pullback_of_model g j d (eSource ≪≫ eModel) hModel
  refine ⟨E, hE, hgeneric.trans ?_⟩
  simp only [Iso.trans_hom, eSource, eModel,
    Inertia.toNormalization_normalizationSourceIso_hom_assoc,
    toNormalization_finiteNormalFieldSourceIso_hom, Iso.refl_hom, Category.id_comp]

end EtaleFundamentalGroups
