/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.CategoryTheory.FilteredColimitFiniteDescent
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer

/-!
# Separated filtered colimits on quasi-compact étale objects

Local equality of two sections of a filtered presheaf colimit can be checked
on finitely many members of an étale covering of a quasi-compact object.
Finite descent for the colimit then implies equality of the sections.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleCohomology

universe u

/-- A locally injective map out of a filtered presheaf colimit of abelian
étale sheaves is injective on every quasi-compact étale object. -/
theorem filteredColimit_app_injective_of_locallyInjective
    {X : Scheme.{u}} {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {G : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (φ : colimit (F ⋙ sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}) ⟶ G)
    [Presheaf.IsLocallyInjective X.smallEtaleTopology φ]
    (U : X.Etale) [QuasiCompact (terminal.from U.left)] :
    Function.Injective (φ.app (op U)) := by
  classical
  let P := colimit (F ⋙ sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u})
  intro s t hst
  let S := Presheaf.equalizerSieve s t
  have hS : S ∈ X.smallEtaleTopology U :=
    Presheaf.equalizerSieve_mem X.smallEtaleTopology φ s t hst
  let A := Σ V : X.Etale, {g : V ⟶ U // S.arrows g}
  let arrow (a : A) : a.1 ⟶ U := a.2.val
  have hSieve : Sieve.ofArrows (fun a : A => a.1) arrow = S := by
    ext V g
    rw [Sieve.mem_ofArrows_iff]
    constructor
    · rintro ⟨a, k, rfl⟩
      exact S.downward_closed a.2.property k
    · intro hg
      exact ⟨⟨V, ⟨g, hg⟩⟩, 𝟙 V, Category.id_comp g⟩
  have hCover : Sieve.ofArrows (fun a : A => a.1) arrow ∈
      X.smallEtaleTopology U := by
    rw [hSieve]
    exact hS
  have hRanges := (Scheme.ofArrows_mem_smallEtaleTopology_iff arrow).mp hCover
  have : CompactSpace U.left :=
    (AlgebraicGeometry.compactSpace_iff_quasiCompact U.left).2 inferInstance
  obtain ⟨K, hK⟩ := (isCompact_univ : IsCompact (Set.univ : Set U.left)).elim_finite_subcover
    (fun a : A => Set.range (arrow a).left)
    (fun a => (arrow a).left.isOpenMap.isOpen_range)
    (by intro x hx; rw [hRanges]; exact Set.mem_univ x)
  let e : ULift.{u} (Fin (Fintype.card K)) ≃ K :=
    Equiv.ulift.trans (Fintype.equivFin K).symm
  let E₀ : PreZeroHypercover.{u} U := {
    I₀ := ULift.{u} (Fin (Fintype.card K))
    X := fun i => (e i).1.1
    f := fun i => arrow (e i).1 }
  have hFiniteCover : ⋃ i : E₀.I₀, Set.range (E₀.f i).left = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hK (Set.mem_univ x))
    obtain ⟨i, hi⟩ := e.surjective ⟨a, ha⟩
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    change x ∈ Set.range (arrow (e i).1).left
    have hi' : (e i).val = a := congrArg Subtype.val hi
    rw [hi']
    exact hxa
  have hE₀ : E₀.sieve₀ ∈ X.smallEtaleTopology U :=
    (Scheme.ofArrows_mem_smallEtaleTopology_iff E₀.f).mpr hFiniteCover
  let E : X.smallEtaleTopology.OneHypercover U :=
    .mk' E₀.toPreOneHypercover hE₀ (by
      intro i j
      exact (sieve₁'_toPreOneHypercover_eq_top E₀ i j).symm ▸
        X.smallEtaleTopology.top_mem _)
  have : Finite E.I₀ := by
    change Finite (ULift.{u} (Fin (Fintype.card K)))
    infer_instance
  have : Finite E.I₁' := by
    change Finite (Σ _ : E₀.I₀ × E₀.I₀, PUnit)
    infer_instance
  have hLimit : IsLimit (E.multifork P) := E.filteredColimitIsLimitMultifork F
  have hUnderlying : IsLimit (E.multifork (P ⋙ forget AddCommGrpCat.{u})) :=
    Multifork.isLimitMapOfPreserves (E.multifork P)
      (forget AddCommGrpCat.{u}) hLimit
  apply ((Multifork.isLimit_types_iff
    (E.multifork (P ⋙ forget AddCommGrpCat.{u}))).mp ⟨hUnderlying⟩).injective
  ext i
  exact (e i).1.2.property

/-- Sheafification of abelian presheaves on the small étale site is locally
bijective, including when the site is larger than the coefficient universe. -/
theorem etaleAbelianToSheafify_locallyBijective (X : Scheme.{u})
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology P) ∧
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology P) := by
  let hPres : X.smallEtaleTopology.PreservesSheafification
      (forget AddCommGrpCat.{u}) :=
    GrothendieckTopology.PreservesSheafification.transport
      X.smallEtaleTopology (Scheme.AffineEtale.topology X) (Scheme.AffineEtale.Spec X)
      (Type u) (forget AddCommGrpCat.{u})
  have hW : X.smallEtaleTopology.W
      (Functor.whiskerRight (toSheafify X.smallEtaleTopology P)
        (forget AddCommGrpCat.{u})) :=
    @GrothendieckTopology.W_of_preservesSheafification X.Etale _
      X.smallEtaleTopology AddCommGrpCat.{u} (Type u) _ _
      (forget AddCommGrpCat.{u}) hPres P
      (sheafify X.smallEtaleTopology P)
      (toSheafify X.smallEtaleTopology P)
      (X.smallEtaleTopology.W_toSheafify P)
  have hBoth := (X.smallEtaleTopology.W_iff_isLocallyBijective
    (A := Type u) (Functor.whiskerRight (toSheafify X.smallEtaleTopology P)
      (forget AddCommGrpCat.{u}))).mp hW
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology
      (Functor.whiskerRight (toSheafify X.smallEtaleTopology P)
        (forget AddCommGrpCat.{u})) := hBoth.2
  refine ⟨(Presheaf.isLocallyInjective_forget_iff X.smallEtaleTopology
    (toSheafify X.smallEtaleTopology P)).mp hBoth.1, ⟨?_⟩⟩
  intro U s
  exact Presheaf.imageSieve_mem X.smallEtaleTopology
    (Functor.whiskerRight (toSheafify X.smallEtaleTopology P)
      (forget AddCommGrpCat.{u})) s

/-- The abelian étale sheafification unit is locally injective. -/
theorem etaleAbelianToSheafify_locallyInjective (X : Scheme.{u})
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology P) :=
  (etaleAbelianToSheafify_locallyBijective X P).1

/-- On a quasi-compact étale object, sheafification introduces no new
equalities between sections of a filtered presheaf colimit of abelian sheaves. -/
theorem filteredColimit_toSheafify_app_injective
    {X : Scheme.{u}} {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (U : X.Etale) [QuasiCompact (terminal.from U.left)] :
    Function.Injective ((toSheafify X.smallEtaleTopology
      (colimit (F ⋙ sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}))).app
        (op U)) := by
  let P := colimit (F ⋙ sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u})
  have : Presheaf.IsLocallyInjective X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology P) :=
    etaleAbelianToSheafify_locallyInjective X P
  exact filteredColimit_app_injective_of_locallyInjective F
    (toSheafify X.smallEtaleTopology P) U

end EtaleCohomology
