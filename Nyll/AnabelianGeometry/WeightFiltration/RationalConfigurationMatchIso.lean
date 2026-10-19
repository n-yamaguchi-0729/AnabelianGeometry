/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.ProjectiveSpace.MatchTriplesSchemeIso
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineBaseChange
import Nyll.AnabelianGeometry.ProjectiveLine.SchemeOpenRestriction

/-! # Rational Configuration Match Iso -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjSpace
open AnabelianGeometry.ProjectiveLine
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AnabelianGeometry.WeightFiltration

theorem rationalConfiguration_schemeIso_of_matchTriples
    (k : Type) [Field k] [Infinite k]
    (sS sT : Finset (Projectivization k (k × k))) (σ : sS ≃ sT)
    (a b c₀ : sS) (hab : a ≠ b) (h₀a : c₀ ≠ a) (h₀b : c₀ ≠ b)
    (hmatch : ∀ c : sS,
      matchTriples a.val b.val c₀.val (σ a).val (σ b).val (σ c₀).val
        (fun h => hab (Subtype.ext h)) (fun h => h₀b (Subtype.ext h))
        (fun h => h₀a (Subtype.ext h))
        (fun h => hab (σ.injective (Subtype.ext h)))
        (fun h => h₀b (σ.injective (Subtype.ext h)))
        (fun h => h₀a (σ.injective (Subtype.ext h))) c.val = (σ c).val) :
    let f : (k × k) ≃ₗ[k] (k × k) :=
      matchTriplesLinearEquiv a.val b.val c₀.val (σ a).val (σ b).val (σ c₀).val
        (fun h => hab (Subtype.ext h)) (fun h => h₀b (Subtype.ext h))
        (fun h => h₀a (Subtype.ext h))
        (fun h => hab (σ.injective (Subtype.ext h)))
        (fun h => h₀b (σ.injective (Subtype.ext h)))
        (fun h => h₀a (σ.injective (Subtype.ext h)))
    (∀ c : sS, projectiveLinearEquiv f c.val = (σ c).val) ∧
    ∃ I : (rationalConfigurationOpen sS : Scheme) ≅
        (rationalConfigurationOpen sT : Scheme),
      I.hom ≫ (rationalConfigurationOpen sT).ι =
        (rationalConfigurationOpen sS).ι ≫ (pairLinearCoordinateIso f).hom ∧
      I.hom ≫ ((rationalConfigurationOpen sT).ι ≫ π k 1) =
        (rationalConfigurationOpen sS).ι ≫ π k 1 := by
  intro f
  have hf : ∀ c : sS, projectiveLinearEquiv f c.val = (σ c).val := by
    intro c
    rw [show projectiveLinearEquiv f =
      matchTriples a.val b.val c₀.val (σ a).val (σ b).val (σ c₀).val
        (fun h => hab (Subtype.ext h)) (fun h => h₀b (Subtype.ext h))
        (fun h => h₀a (Subtype.ext h))
        (fun h => hab (σ.injective (Subtype.ext h)))
        (fun h => h₀b (σ.injective (Subtype.ext h)))
        (fun h => h₀a (σ.injective (Subtype.ext h))) from
      projectiveLinearEquiv_matchTriplesLinearEquiv _ _ _ _ _ _ _ _ _ _ _ _]
    exact hmatch c
  let e : projectiveLineScheme k ≅ projectiveLineScheme k := pairLinearCoordinateIso f
  have hpoint (c : sS) : e.hom (projectiveRationalPoint c.val) =
      projectiveRationalPoint (σ c).val := by
    change (pairLinearCoordinateIso f).hom (projectiveRationalPoint c.val) = _
    rw [pairLinearCoordinateIso_projectiveRationalPoint, hf c]
  have hopen : e.hom ⁻¹ᵁ rationalConfigurationOpen sT =
      rationalConfigurationOpen sS := by
    ext x
    change e.hom x ∈ rationalConfigurationOpen sT ↔ x ∈ rationalConfigurationOpen sS
    rw [mem_rationalConfigurationOpen_iff, mem_rationalConfigurationOpen_iff]
    constructor
    · intro hx p hp heq
      apply hx (σ ⟨p, hp⟩).val (σ ⟨p, hp⟩).property
      exact (congrArg e.hom heq).trans (hpoint ⟨p, hp⟩)
    · intro hx p hp heq
      let c : sS := σ.symm ⟨p, hp⟩
      have hc : (σ c).val = p := congrArg Subtype.val (σ.apply_symm_apply ⟨p, hp⟩)
      apply hx c.val c.property
      apply e.hom.homeomorph.injective
      exact heq.trans ((hpoint c).trans (congrArg projectiveRationalPoint hc)).symm
  refine ⟨hf, restrictSchemeIso e (rationalConfigurationOpen sS)
    (rationalConfigurationOpen sT) hopen, ?_, ?_⟩
  · exact restrictSchemeIso_hom_ι e (rationalConfigurationOpen sS)
      (rationalConfigurationOpen sT) hopen
  · exact restrictSchemeIso_over e (π k 1) (π k 1)
      (linearCoordinateIso_hom_comp_π (finCoordinateEquiv f))
      (rationalConfigurationOpen sS) (rationalConfigurationOpen sT) hopen

end AnabelianGeometry.WeightFiltration
