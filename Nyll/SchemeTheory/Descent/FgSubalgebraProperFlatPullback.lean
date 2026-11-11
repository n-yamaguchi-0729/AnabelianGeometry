/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Tower
public import Nyll.SchemeTheory.Descent.FgSubalgebraPullbackFinitePresentation
public import Nyll.SchemeTheory.Descent.IsSeparatedFgSubalgebra
public import Nyll.SchemeTheory.Descent.FlatFgSubalgebraFlatPullbackSnd
public import Nyll.SchemeTheory.Descent.IsProperFgSubalgebraProperPullbackSnd
public import Nyll.SchemeTheory.Descent.SmoothFgSubalgebraSmoothPullbackSnd

/-!
# exists fg subalgebra is Proper flat is Pullback of is Proper of flat of locally Of Finite
Presentation
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.ProperFlatFinitePresentationDescent
attribute [-instance] IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
  AlgebraicGeometry.SubalgebraStages.compactSpace_pullback
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback
  AlgebraicGeometry.SubalgebraStages.compactSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiCompact_snd
  AlgebraicGeometry.SubalgebraStages.isAffineHom_leg
  AlgebraicGeometry.SubalgebraStages.isAffineHom_trans
  AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map
  AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd
  AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
attribute [-simp] IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply
  IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of
  IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app
  AlgebraicGeometry.SubalgebraStages.specLeg_specHom
  AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt
  AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj
  AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map
  AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd
  AlgebraicGeometry.SubalgebraStages.specTrans_specHom
  AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app
  AlgebraicGeometry.SubalgebraStages.specDiagram_map
  AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst
  AlgebraicGeometry.SubalgebraStages.leg_trans AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace ApproxAux

lemma iff_of_isPullback {P : MorphismProperty Scheme.{u}} [P.RespectsIso] {X X₁ Y B : Scheme.{u}}
    {π : X ⟶ X₁} {g : X ⟶ Y} {f : X₁ ⟶ B} {ι : Y ⟶ B} (sq : IsPullback π g f ι) :
    P (pullback.snd f ι) ↔ P g := by
  rw [← sq.isoPullback_hom_snd, P.cancel_left_of_respectsIso]

lemma exists_isPullback_of_fac {X X₁ Y B B' : Scheme.{u}} {π : X ⟶ X₁} {g : X ⟶ Y} {f : X₁ ⟶ B} {ι
  : Y ⟶ B}
    (sq : IsPullback π g f ι) (κ : B' ⟶ B) (ι' : Y ⟶ B') (hι : ι' ≫ κ = ι) :
    ∃ π' : X ⟶ pullback f κ, IsPullback π' g (pullback.snd f κ) ι' := by
  have w : π ≫ f = (g ≫ ι') ≫ κ := by rw [Category.assoc, hι]; exact sq.w
  refine ⟨pullback.lift π (g ≫ ι') w, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst f κ) (v₁₃ := f) (h₂₂ := κ) ?_ (pullback.lift_snd
    _ _ _)
    (IsPullback.of_hasPullback f κ)
  rw [pullback.lift_fst, hι]
  exact sq

lemma specMap_algebraMap_comp {T : Type u} [CommRing T] {A : Type u} [CommRing A] [Algebra T A]
    (T' : Subalgebra T A) :
    Spec.map (CommRingCat.ofHom (algebraMap ↥T' A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap T
      ↥T')) =
      Spec.map (CommRingCat.ofHom (algebraMap T A)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

lemma package {A₀ B A : Type u} [CommRing A₀] [CommRing B] [CommRing A] [Algebra A₀ B] [Algebra B
  A] [Algebra A₀ A]
    [IsScalarTower A₀ B A] [Algebra.FiniteType A₀ B]
    (T₄ : Subalgebra B A) (hT₄ : T₄.FG) (s : Finset A) (hs : (↑s : Set A) ⊆ (T₄.restrictScalars A₀
      : Set A))
    {X X₀ : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of A)) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T₄)) (π
      : X ⟶ X₀)
    (h1 : IsProper f₀) (h2 : Flat f₀)
    (h3 : IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T₄ A)))) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : X ⟶ X₀),
        IsProper f₀ ∧ Flat f₀ ∧ IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A)))
          := by
  have : Algebra.FiniteType B ↥T₄ := (Subalgebra.fg_iff_finiteType _).mp hT₄
  have hFT : Algebra.FiniteType A₀ ↥T₄ := Algebra.FiniteType.trans (S := B) inferInstance
    inferInstance
  exact ⟨T₄.restrictScalars A₀, (Subalgebra.fg_iff_finiteType _).mpr hFT, hs, X₀, f₀, π, h1, h2, h3⟩

end ApproxAux

open ApproxAux in
/-- A separated finitely presented morphism descends to an actual finite-type
coefficient subalgebra with its original base-change square. -/
theorem _root_.AlgebraicGeometry.SeparatedFinitePresentationDescent
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of A)) [IsSeparated g]
    [QuasiCompact g] [LocallyOfFinitePresentation g] (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : X ⟶ X₀),
        IsSeparated f₀ ∧ QuasiCompact f₀ ∧ LocallyOfFinitePresentation f₀ ∧
          IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) := by
  classical
  obtain ⟨T₁, hT₁, hsT₁, X₁, f₁, π₁, hlfp₁, hqc₁, hqs₁, sq₁⟩ :=
    exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation (A₀ := A₀) g s
  have := hlfp₁
  have := hqc₁
  have := hqs₁
  have : Algebra.FiniteType A₀ ↥T₁ := (Subalgebra.fg_iff_finiteType _).mp hT₁
  have : IsSeparated (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ A)))) :=
    (iff_of_isPullback (P := @IsSeparated) sq₁).mpr inferInstance
  obtain ⟨T₂, hT₂, -, hsep₂⟩ :=
    IsSeparated.exists_fg_subalgebra_of_isSeparated_pullback_snd (A := A) f₁ ∅
  have := hsep₂
  have : Algebra.FiniteType ↥T₁ ↥T₂ := (Subalgebra.fg_iff_finiteType _).mp hT₂
  have hFT : Algebra.FiniteType A₀ ↥T₂ :=
    Algebra.FiniteType.trans (S := ↥T₁) inferInstance inferInstance
  let κ₂ : Spec (CommRingCat.of ↥T₂) ⟶ Spec (CommRingCat.of ↥T₁) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))
  let f₂ : pullback f₁ κ₂ ⟶ Spec (CommRingCat.of ↥T₂) := pullback.snd f₁ κ₂
  obtain ⟨π₂, sq₂⟩ := exists_isPullback_of_fac sq₁ κ₂
    (Spec.map (CommRingCat.ofHom (algebraMap ↥T₂ A))) (specMap_algebraMap_comp T₂)
  have : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    locallyOfFinitePresentation_isStableUnderBaseChange
  have hlfp₂ : LocallyOfFinitePresentation f₂ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback f₁ κ₂) hlfp₁
  have : LocallyOfFinitePresentation f₂ := hlfp₂
  have : MorphismProperty.IsStableUnderBaseChange
      (@QuasiCompact : MorphismProperty Scheme.{u}) := quasiCompact_isStableUnderBaseChange
  have hqc₂ : QuasiCompact f₂ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@QuasiCompact : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback f₁ κ₂) hqc₁
  refine ⟨T₂.restrictScalars A₀, (Subalgebra.fg_iff_finiteType _).mpr hFT,
    ?_, _, f₂, π₂, hsep₂, hqc₂, hlfp₂, sq₂⟩
  intro a ha
  exact T₂.algebraMap_mem (⟨a, hsT₁ ha⟩ : ↥T₁)

open ApproxAux in
/-- A proper finitely presented morphism descends to an actual finite-type
coefficient subalgebra. Flatness is not required. -/
theorem _root_.AlgebraicGeometry.ProperFinitePresentationDescent
    {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of A)) [IsProper g]
    [LocallyOfFinitePresentation g] (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : X ⟶ X₀),
        IsProper f₀ ∧ LocallyOfFinitePresentation f₀ ∧
          IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) := by
  classical
  obtain ⟨T₁, hT₁, hsT₁, X₁, f₁, π₁, hsep₁, hqc₁, hlfp₁, sq₁⟩ :=
    SeparatedFinitePresentationDescent (A₀ := A₀) g s
  have : IsSeparated f₁ := hsep₁
  have : QuasiCompact f₁ := hqc₁
  have : LocallyOfFinitePresentation f₁ := hlfp₁
  have : Algebra.FiniteType A₀ ↥T₁ := (Subalgebra.fg_iff_finiteType _).mp hT₁
  have : IsNoetherianRing ↥T₁ := Algebra.FiniteType.isNoetherianRing A₀ ↥T₁
  have : IsProper (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ A)))) :=
    (iff_of_isPullback (P := @IsProper) sq₁).mpr inferInstance
  obtain ⟨T₂, hT₂, -, hprop₂⟩ :=
    IsProper.exists_fg_subalgebra_of_isProper_pullback_snd (A := A) f₁ ∅
  let κ₂ : Spec (CommRingCat.of ↥T₂) ⟶ Spec (CommRingCat.of ↥T₁) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))
  let f₂ := pullback.snd f₁ κ₂
  have hlfp₂ : LocallyOfFinitePresentation f₂ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback f₁ κ₂) hlfp₁
  obtain ⟨π₂, sq₂⟩ := exists_isPullback_of_fac sq₁ κ₂
    (Spec.map (CommRingCat.ofHom (algebraMap ↥T₂ A))) (specMap_algebraMap_comp T₂)
  have : Algebra.FiniteType ↥T₁ ↥T₂ := (Subalgebra.fg_iff_finiteType _).mp hT₂
  have hFT : Algebra.FiniteType A₀ ↥T₂ :=
    Algebra.FiniteType.trans (S := ↥T₁) inferInstance inferInstance
  refine ⟨T₂.restrictScalars A₀, (Subalgebra.fg_iff_finiteType _).mpr hFT,
    ?_, _, f₂, π₂, hprop₂, hlfp₂, sq₂⟩
  intro a ha
  exact T₂.algebraMap_mem (⟨a, hsT₁ ha⟩ : ↥T₁)

open ApproxAux in
theorem _root_.AlgebraicGeometry.ProperFlatFinitePresentationDescent
    {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of A)) [IsProper g] [Flat g]
      [LocallyOfFinitePresentation g]
    (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : X ⟶ X₀),
        IsProper f₀ ∧ Flat f₀ ∧ IsPullback π g f₀
          (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) := by
  classical
  obtain ⟨T₁, hT₁, hsT₁, X₁, f₁, π₁, hprop₁, hlfp₁, sq₁⟩ :=
    ProperFinitePresentationDescent (A₀ := A₀) g s
  have : IsProper f₁ := hprop₁
  have : LocallyOfFinitePresentation f₁ := hlfp₁
  have : Algebra.FiniteType A₀ ↥T₁ := (Subalgebra.fg_iff_finiteType _).mp hT₁
  have : MorphismProperty.IsStableUnderBaseChange
      (@Flat : MorphismProperty Scheme.{u}) := Flat.isStableUnderBaseChange
  have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := (@Flat : MorphismProperty Scheme.{u}))
  have : Flat (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ A)))) :=
    (iff_of_isPullback (P := @Flat) sq₁).mpr inferInstance
  obtain ⟨T₂, hT₂, -, hflat₂⟩ :=
    Flat.exists_fg_subalgebra_of_flat_pullback_snd (A := A) f₁ ∅
  let κ₂ : Spec (CommRingCat.of ↥T₂) ⟶ Spec (CommRingCat.of ↥T₁) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))
  let f₂ := pullback.snd f₁ κ₂
  have hprop₂ : IsProper f₂ := inferInstance
  obtain ⟨π₂, sq₂⟩ := exists_isPullback_of_fac sq₁ κ₂
    (Spec.map (CommRingCat.ofHom (algebraMap ↥T₂ A))) (specMap_algebraMap_comp T₂)
  refine package T₂ hT₂ s ?_ g f₂ π₂ hprop₂ hflat₂ sq₂
  intro a ha
  exact T₂.algebraMap_mem (⟨a, hsT₁ ha⟩ : ↥T₁)

open ApproxAux in
/-- A proper smooth scheme descends to a proper smooth finite-type
coefficient model, retaining its original Cartesian generic square. -/
theorem _root_.AlgebraicGeometry.ProperSmoothFinitePresentationDescent
    {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀]
    {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of A)) [IsProper g] [Smooth g] (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (.of T)) (π : X ⟶ X₀),
        IsProper f₀ ∧ Smooth f₀ ∧
          IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap T A))) := by
  obtain ⟨T₁, hT₁, hsT₁, X₁, f₁, π₁, hprop₁, hlfp₁, sq₁⟩ :=
    ProperFinitePresentationDescent (A₀ := A₀) g s
  have : IsProper f₁ := hprop₁
  have : LocallyOfFinitePresentation f₁ := hlfp₁
  have : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @Smooth)
  have : Smooth (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap T₁ A)))) :=
    (iff_of_isPullback (P := @Smooth) sq₁).mpr inferInstance
  obtain ⟨T₂, hT₂, _, hsm₂⟩ := Smooth.exists_fg_subalgebra_of_smooth_pullback_snd (A := A) f₁ ∅
  let κ₂ : Spec (.of T₂) ⟶ Spec (.of T₁) :=
    Spec.map (CommRingCat.ofHom (algebraMap T₁ T₂))
  let f₂ := pullback.snd f₁ κ₂
  have hprop₂ : IsProper f₂ := by
    dsimp only [f₂]
    infer_instance
  obtain ⟨π₂, sq₂⟩ := exists_isPullback_of_fac sq₁ κ₂
    (Spec.map (CommRingCat.ofHom (algebraMap T₂ A))) (specMap_algebraMap_comp T₂)
  have : Algebra.FiniteType A₀ T₁ := (Subalgebra.fg_iff_finiteType T₁).mp hT₁
  have : Algebra.FiniteType T₁ T₂ := (Subalgebra.fg_iff_finiteType T₂).mp hT₂
  have hFT : Algebra.FiniteType A₀ T₂ :=
    Algebra.FiniteType.trans (S := T₁) inferInstance inferInstance
  refine ⟨T₂.restrictScalars A₀, (Subalgebra.fg_iff_finiteType _).mpr hFT,
    ?_, _, f₂, π₂, hprop₂, hsm₂, sq₂⟩
  intro z hz
  exact T₂.algebraMap_mem (⟨z, hsT₁ hz⟩ : T₁)

end AlgebraicCurves.Geometry.Schemes.Proofs.ProperFlatFinitePresentationDescent
end ProofImplementation
