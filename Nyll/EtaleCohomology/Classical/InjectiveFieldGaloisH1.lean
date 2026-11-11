/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FieldSectionRepresentations
public import Nyll.EtaleCohomology.Sites.GaloisCechSections
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FieldCoverQuotient

/-!
# Degree-one Galois acyclicity of actual injective sheaf sections

The geometric Cech primitive theorem supplies the coboundary. The
field/deck comparison transports its actual action to the bundled
Galois representation, without assuming injectivity after restriction.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.FiniteEtale

namespace EtaleCohomology

/-- A cocycle for the actual field action on an injective sheaf has
an actual section primitive. -/
theorem exists_injective_fieldGalois_cocycle_primitive
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) [Injective F]
    (c : Gal(L/K) → F.obj.obj
      (op ((finiteEtaleInclusion (Spec (.of K))).obj (FiniteEtale.mk (ξ K L)))))
    (hc : ∀ σ τ, c (σ * τ) = (fieldGaloisSheafAction K L F σ).asIso.hom (c τ) + c σ) :
    ∃ s, ∀ σ : Gal(L/K), (fieldGaloisSheafAction K L F σ).asIso.hom s - s = c σ := by
  let Y : FiniteEtale (Spec (.of K)) := FiniteEtale.mk (ξ K L)
  have : CategoryTheory.PreGaloisCategory.IsGalois Y :=
    EtaleFundamentalGroups.fieldFiniteEtaleCover_isGalois K L
  let e := EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L
  let d (σ : Aut Y) := c (e.symm (MulOpposite.op σ))
  have ha (σ : Aut Y) (s : F.obj.obj (op ((finiteEtaleInclusion (Spec (.of K))).obj Y))) :
      (fieldGaloisSheafAction K L F (e.symm (MulOpposite.op σ))).asIso.hom s =
        F.obj.map ((finiteEtaleInclusion (Spec (.of K))).map σ.asIso.hom).op s := by
    change (finiteEtaleSheafDeckAction (Spec (.of K)) F Y
      (e (e.symm (MulOpposite.op σ)))).asIso.hom s = _
    rw [e.apply_symm_apply]
    rfl
  have hd : ∀ σ τ : Aut Y, d (τ * σ) =
      F.obj.map ((finiteEtaleInclusion (Spec (.of K))).map σ.asIso.hom).op (d τ) + d σ := by
    intro σ τ
    change c (e.symm (MulOpposite.op (τ * σ))) = _
    rw [MulOpposite.op_mul, e.symm.map_mul, hc, ha]
  obtain ⟨s, hs⟩ := exists_injective_galois_cocycle_primitive
    (Spec (.of K)) F Y d hd
  refine ⟨s, ?_⟩
  intro σ
  have h := hs (MulOpposite.unop (e σ))
  have he : e.symm (MulOpposite.op (MulOpposite.unop (e σ))) = σ := by
    rw [MulOpposite.op_unop, e.symm_apply_apply]
  have hact := ha (MulOpposite.unop (e σ)) s
  rw [he] at hact
  rw [hact]
  exact h.trans (congrArg c he)

/-- The actual field-section representation of an injective etale sheaf
has zero first group cohomology. -/
theorem fieldGaloisSheafSections_H1_eq_zero_of_injective
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{0}) [Injective F]
    (x : groupCohomology (fieldGaloisSheafSectionsRep K L F) 1) : x = 0 := by
  refine groupCohomology.H1_induction_on x ?_
  intro c
  apply (groupCohomology.H1π_eq_zero_iff c).mpr
  obtain ⟨s, hs⟩ := exists_injective_fieldGalois_cocycle_primitive K L F c
    ((groupCohomology.mem_cocycles₁_iff c).mp c.property)
  change ∃ s, (groupCohomology.d₀₁ (fieldGaloisSheafSectionsRep K L F)).hom s = ⇑c
  refine ⟨s, ?_⟩
  funext σ
  exact hs σ

end EtaleCohomology
