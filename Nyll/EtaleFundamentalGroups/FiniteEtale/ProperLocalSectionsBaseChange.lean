/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_finite_projective_sections_and_exists_linearEquiv_tensorProduct_pullbackLocalSection_of_forall_subsingleton_HSucc.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


module

public import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperLocalH0BaseChange
public import Nyll.AlgebraicCurves.Cohomology.ProjectiveSectionsBaseChange
public import Nyll.AlgebraicCurves.Cohomology.Sheaves.BaseChange.CochainBaseChangeEquiv
public import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChart.SectionsOf
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech

/-!
# Actual section base change for proper geometrically reduced local families

The closed-fibre theorem supplies finite projectivity and kernel base change
without a reduced-base or higher-cohomology-vanishing assumption. The final
section/cochain construction is adapted from the attributed FLT source above.
It retains the exact formula on pure tensors of actual global sections.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

universe u

open Scheme.TwoAffineOpenCover
open OModulePresheaf
  (sectionsEquivH0
    finite_projective_H0_and_bijective_baseChange_of_proper_flat_of_etale_closedFiber)

/-- Étaleness of closed-fibre sections gives finite projective global sections
and arbitrary base change, with the actual pullback-unit formula. -/
theorem finite_projective_sections_and_baseChange_of_proper_flat_of_etale_closedFiber
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f]
    (hEtaleFiber : (pullback.snd f
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).appTop.hom.Etale) :
    let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let : Module R Γ(M, ⊤) := moduleSectionsOfHom f M ⊤
    (Module.Finite R Γ(M, ⊤) ∧ Module.Projective R Γ(M, ⊤)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        let : Module A Γ((Scheme.Modules.pullback
            (pullback.fst f (specMap R A))).obj M, ⊤) :=
          moduleSectionsOfHom (pullback.snd f (specMap R A))
            ((Scheme.Modules.pullback (pullback.fst f (specMap R A))).obj M) ⊤
        ∃ e : A ⊗[R] Γ(M, ⊤) ≃ₗ[A]
            Γ((Scheme.Modules.pullback (pullback.fst f (specMap R A))).obj M, ⊤),
          ∀ (a : A) (s : Γ(M, ⊤)), e (a ⊗ₜ[R] s) =
            a • (show Γ((Scheme.Modules.pullback
                (pullback.fst f (specMap R A))).obj M, ⊤) from
              pullbackLocalSection (pullback.fst f (specMap R A)) s) := by
  intro M hRΓ
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := _root_.AlgebraicGeometry.Scheme.OrderedAffineCover.ofCompact X
  let F := OModulePresheaf.ofModules f M
  have htriv := (Scheme.Modules.isInvertible_unit X).exists_trivialization
  obtain ⟨hfin, hproj, hbij⟩ :=
    finite_projective_H0_and_bijective_baseChange_of_proper_flat_of_etale_closedFiber
      f 𝒰 hEtaleFiber
  let ε₀ : Γ(M, ⊤) ≃ₗ[R] F.H0 𝒰 := sectionsEquivH0 f M 𝒰
  have : Module.Finite R (F.H0 𝒰) := hfin
  have : Module.Projective R (F.H0 𝒰) := hproj
  refine ⟨⟨Module.Finite.equiv ε₀.symm, Module.Projective.of_equiv ε₀.symm⟩, ?_⟩
  intro A _ _ hAΓ
  exact OModulePresheaf.exists_sectionsBaseChangeEquiv_of_bijective_ker f 𝒰 M htriv A (hbij A)

/-- For the actual structure sheaf, proper flat geometrically reduced families
over a Noetherian local ring have finite projective global sections and an
arbitrary base-change equivalence with the actual pullback-unit formula. -/
theorem finite_projective_sections_and_baseChange_of_proper_flat_geometricallyReduced_local
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [GeometricallyReduced f] :
    let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let : Module R Γ(M, ⊤) := moduleSectionsOfHom f M ⊤
    (Module.Finite R Γ(M, ⊤) ∧ Module.Projective R Γ(M, ⊤)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        let : Module A Γ((Scheme.Modules.pullback
            (pullback.fst f (specMap R A))).obj M, ⊤) :=
          moduleSectionsOfHom (pullback.snd f (specMap R A))
            ((Scheme.Modules.pullback (pullback.fst f (specMap R A))).obj M) ⊤
        ∃ e : A ⊗[R] Γ(M, ⊤) ≃ₗ[A]
            Γ((Scheme.Modules.pullback (pullback.fst f (specMap R A))).obj M, ⊤),
          ∀ (a : A) (s : Γ(M, ⊤)), e (a ⊗ₜ[R] s) =
            a • (show Γ((Scheme.Modules.pullback
                (pullback.fst f (specMap R A))).obj M, ⊤) from
              pullbackLocalSection (pullback.fst f (specMap R A)) s) := by
  exact finite_projective_sections_and_baseChange_of_proper_flat_of_etale_closedFiber f
    (finite_etale_appTop_of_isProper_of_geometricallyReduced_overField
      (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).2

end AlgebraicGeometry.Scheme.Modules
