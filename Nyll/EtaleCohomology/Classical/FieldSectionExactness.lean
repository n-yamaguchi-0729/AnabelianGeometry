/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FieldSectionRepresentations
public import Nyll.EtaleCohomology.Classical.FieldUnitSections

/-!
# Exactness of actual unit-kernel Galois representations

Left exactness comes from actual sheaf evaluation. Surjectivity is the
geometric Hilbert 90 section-lifting theorem on the field neighborhood.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale

namespace EtaleCohomology

private abbrev representationUnderlyingAbelian
    (R : Type) [Ring R] (G : Type u) [Monoid G] :
    Rep.{u} R G ⥤ AddCommGrpCat.{u} :=
  forget₂ (Rep.{u} R G) (ModuleCat.{u} R) ⋙
    forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

private theorem representation_exact_iff_underlying
    (R : Type) [Ring R] (G : Type u) [Monoid G]
    (S : ShortComplex (Rep.{u} R G)) :
    (S.map (representationUnderlyingAbelian R G)).Exact ↔ S.Exact :=
  S.exact_map_iff_of_faithful (representationUnderlyingAbelian R G)

/-- Actual finite-Galois field sections preserve short exact sequences
whose kernel is the actual multiplicative-group sheaf. -/
theorem fieldGaloisSheafSections_unitsKernel_shortExact
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {B Q : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (i : etaleMultiplicativeGroupSheaf (Spec (.of K)) ⟶ B) (p : B ⟶ Q)
    (hz : i ≫ p = 0) (hS : (ShortComplex.mk i p hz).ShortExact) :
    ((ShortComplex.mk i p hz).map (fieldGaloisSheafSectionsFunctor K L)).ShortExact := by
  let X := Spec (.of K)
  let V := (finiteEtaleInclusion X).obj (FiniteEtale.mk (ξ K L))
  let S := ShortComplex.mk i p hz
  let Γ : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let R := fieldGaloisSheafSectionsFunctor K L
  have hΓ : (S.map Γ).Exact :=
    hS.exact.map_of_mono_of_preservesKernel Γ hS.mono_f inferInstance
  have : Mono i := hS.mono_f
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (representation_exact_iff_underlying ℤ Gal(L/K) (S.map R)).mp
    change (S.map Γ).Exact
    exact hΓ
  · apply (Rep.mono_iff_injective _).mpr
    change Function.Injective (i.hom.app (op V))
    exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  · apply (Rep.epi_iff_surjective _).mpr
    intro q
    exact exists_section_lift_of_units_kernel_at_field X L (ξ K L) i p hz hS q

end EtaleCohomology
