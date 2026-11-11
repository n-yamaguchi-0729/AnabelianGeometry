/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.FilteredColimitSectionInjectivity
public import Nyll.EtaleCohomology.Sites.FiniteAffineSectionLifts
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered

/-!
# Gluing finite local lifts in filtered colimits

Local lifts of a section through a locally injective map from a filtered
presheaf colimit glue along a finite étale covering with quasi-compact
pairwise intersections. Equality on the intersections is reflected by the
section-injectivity theorem, and finite descent supplies the global lift.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleCohomology

universe u

/-- Finite local lifts through a locally injective map from a filtered
colimit glue if the pairwise covering intersections are quasi-compact. -/
theorem filteredColimit_exists_lift_of_finite_cover
    {X : Scheme.{u}} {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (φ : colimit (F ⋙ sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}) ⟶ G.obj)
    [Presheaf.IsLocallyInjective X.smallEtaleTopology φ]
    {U : X.Etale} {ι : Type u} [Finite ι]
    (V : ι → X.Etale) (f : ∀ i, V i ⟶ U)
    (hcover : Sieve.ofArrows V f ∈ X.smallEtaleTopology U)
    (hqc : ∀ i j, QuasiCompact (terminal.from (pullback (f i) (f j)).left))
    (a : G.obj.obj (op U))
    (t : ∀ i, (colimit (F ⋙ sheafToPresheaf
      X.smallEtaleTopology AddCommGrpCat.{u})).obj (op (V i)))
    (ht : ∀ i, φ.app (op (V i)) (t i) = G.obj.map (f i).op a) :
    ∃ s, φ.app (op U) s = a := by
  classical
  let P := colimit (F ⋙ sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u})
  let E₀ : PreZeroHypercover.{u} U := { I₀ := ι, X := V, f := f }
  let E : X.smallEtaleTopology.OneHypercover U :=
    .mk' E₀.toPreOneHypercover hcover (by
      intro i j
      exact (sieve₁'_toPreOneHypercover_eq_top E₀ i j).symm ▸
        X.smallEtaleTopology.top_mem _)
  have : Finite E.I₀ := inferInstanceAs (Finite ι)
  have : Finite E.I₁' := by
    change Finite (Σ _ : ι × ι, PUnit)
    infer_instance
  have hcompat (i j : ι) :
      P.map (pullback.fst (f i) (f j)).op (t i) =
        P.map (pullback.snd (f i) (f j)).op (t j) := by
    have : QuasiCompact (terminal.from (pullback (f i) (f j)).left) := hqc i j
    apply filteredColimit_app_injective_of_locallyInjective F φ (pullback (f i) (f j))
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ht i, ht j]
    simp only [← ConcreteCategory.comp_apply, ← G.obj.map_comp, ← op_comp,
      pullback.condition]
  have hLimit : IsLimit (E.multifork P) := E.filteredColimitIsLimitMultifork F
  have hUnderlying : IsLimit (E.multifork (P ⋙ forget AddCommGrpCat.{u})) :=
    Multifork.isLimitMapOfPreserves (E.multifork P)
      (forget AddCommGrpCat.{u}) hLimit
  let family : (E.multicospanIndex (P ⋙ forget AddCommGrpCat.{u})).sections := {
    val := t
    property := by
      rintro ⟨⟨i, j⟩, ⟨⟩⟩
      exact hcompat i j }
  let s : P.obj (op U) := Multifork.IsLimit.sectionsEquiv hUnderlying family
  have hs (i : ι) : P.map (f i).op s = t i :=
    Multifork.IsLimit.sectionsEquiv_apply_val hUnderlying family i
  have hImage (i : ι) : G.obj.map (f i).op (φ.app (op U) s) =
      G.obj.map (f i).op a := by
    rw [← NatTrans.naturality_apply, hs i, ht i]
  refine ⟨s, ?_⟩
  apply G.isSeparated U (Sieve.ofArrows V f) hcover (φ.app (op U) s) a
  intro W g hg
  obtain ⟨i, k, rfl⟩ := (Sieve.mem_ofArrows_iff V f g).mp hg
  rw [op_comp, G.obj.map_comp, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply]
  exact congrArg (G.obj.map k.op) (hImage i)

/-- Pairwise pullbacks of affine étale objects over a quasi-separated
object are quasi-compact. -/
theorem etale_affine_overlap_quasiCompact
    {X : Scheme.{u}} {U V W : X.Etale} (f : V ⟶ U) (g : W ⟶ U)
    [IsAffine V.left] [IsAffine W.left] [QuasiSeparatedSpace U.left] :
    QuasiCompact (terminal.from (pullback f g).left) := by
  let L := Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X
  have hp : IsPullback (pullback.fst f g).left (pullback.snd f g).left f.left g.left :=
    (IsPullback.of_hasPullback f g).map L
  have : QuasiCompact g.left := inferInstance
  have : QuasiCompact (pullback.fst f g).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip inferInstance
  have : CompactSpace (pullback f g).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f g).left
  exact (AlgebraicGeometry.compactSpace_iff_quasiCompact (pullback f g).left).1
    inferInstance

/-- Local bijectivity onto a sheaf gives surjectivity on sections of a
quasi-compact, quasi-separated étale object for a filtered presheaf colimit. -/
theorem filteredColimit_app_surjective_of_locallyBijective
    {X : Scheme.{u}} {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (φ : colimit (F ⋙ sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}) ⟶ G.obj)
    [Presheaf.IsLocallyInjective X.smallEtaleTopology φ]
    [Presheaf.IsLocallySurjective X.smallEtaleTopology φ]
    (U : X.Etale) [QuasiCompact (terminal.from U.left)]
    [QuasiSeparatedSpace U.left] : Function.Surjective (φ.app (op U)) := by
  classical
  intro a
  obtain ⟨K, V, f, hV, hcover, ht⟩ :=
    exists_finite_affine_cover_section_lifts φ a
      (Presheaf.imageSieve_mem X.smallEtaleTopology φ a)
  choose t ht using ht
  have hqc (i j : K) : QuasiCompact (terminal.from (pullback (f i) (f j)).left) := by
    have : IsAffine (V i).left := hV i
    have : IsAffine (V j).left := hV j
    exact etale_affine_overlap_quasiCompact (f i) (f j)
  exact filteredColimit_exists_lift_of_finite_cover F G φ V f hcover hqc a t ht

/-- Sheafification is bijective on sections of a filtered presheaf colimit
over any quasi-compact, quasi-separated étale object. -/
theorem filteredColimit_toSheafify_app_bijective
    {X : Scheme.{u}} {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (U : X.Etale) [QuasiCompact (terminal.from U.left)]
    [QuasiSeparatedSpace U.left] :
    Function.Bijective ((toSheafify X.smallEtaleTopology
      (colimit (F ⋙ sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}))).app
        (op U)) := by
  let P := colimit (F ⋙ sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u})
  let G := (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj P
  have : Presheaf.IsLocallyInjective X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology P) :=
    (etaleAbelianToSheafify_locallyBijective X P).1
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology P) :=
    (etaleAbelianToSheafify_locallyBijective X P).2
  exact ⟨filteredColimit_toSheafify_app_injective F U,
    filteredColimit_app_surjective_of_locallyBijective F G
      (toSheafify X.smallEtaleTopology P) U⟩

/-- Sections over a quasi-compact, quasi-separated étale object preserve
the actual sheaf colimit of any small filtered diagram. -/
theorem preservesColimit_etaleSheafSections
    {X : Scheme.{u}} {I : Type u} [SmallCategory I] [IsFiltered I]
    (U : X.Etale) [QuasiCompact (terminal.from U.left)]
    [QuasiSeparatedSpace U.left]
    (F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    PreservesColimit F
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op U)) := by
  let J := X.smallEtaleTopology
  let P := F ⋙ sheafToPresheaf J AddCommGrpCat.{u}
  let E : Cocone P := colimit.cocone P
  let S : Cocone F := Sheaf.sheafifyCocone E
  let Ev := (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj (op U)
  let Γ := (sheafSections J AddCommGrpCat.{u}).obj (op U)
  have hη : IsIso ((toSheafify J E.pt).app (op U)) :=
    (ConcreteCategory.isIso_iff_bijective ((toSheafify J E.pt).app (op U))).mpr
    (filteredColimit_toSheafify_app_bijective F U)
  have hE : IsColimit E := colimit.isColimit P
  have hS : IsColimit S := Sheaf.isColimitSheafifyCocone E hE
  have e : Ev.mapCocone E ≅ Γ.mapCocone S := by
    refine Cocone.ext (@asIso AddCommGrpCat.{u} _ _ _
      ((toSheafify J E.pt).app (op U)) hη) ?_
    intro i
    change (E.ι.app i).app (op U) ≫ (toSheafify J E.pt).app (op U) =
      ((Sheaf.sheafifyCocone E).ι.app i).hom.app (op U)
    rw [Sheaf.sheafifyCocone_ι_app_val, NatTrans.comp_app]
  exact preservesColimit_of_preserves_colimit_cocone hS
    ((isColimitOfPreserves Ev hE).ofIsoColimit e)

/-- Étale sections over a quasi-compact, quasi-separated object commute
with small filtered colimits of abelian sheaves. -/
theorem preservesFilteredColimits_etaleSheafSections
    {X : Scheme.{u}} (U : X.Etale) [QuasiCompact (terminal.from U.left)]
    [QuasiSeparatedSpace U.left] :
    PreservesFilteredColimitsOfSize.{u, u}
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op U)) where
  preserves_filtered_colimits I _ _ :=
    ⟨fun {F} => preservesColimit_etaleSheafSections (I := I) U F⟩

end EtaleCohomology
