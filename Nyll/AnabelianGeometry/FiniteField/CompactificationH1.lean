/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.AdicPullback
import Nyll.AnabelianGeometry.WeightFiltration.CompactCharacterDescent
import Nyll.EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective

/-!
# Actual rational H¹ of the compactification inside open-curve H¹

An open immersion into a normal integral locally noetherian scheme induces
a surjection on the actual fundamental groups. Rational cohomology classes
come from that scheme exactly when their actual characters kill its kernel.

This result works in every characteristic and uses no trace formula. It does
not assert that a mixed arithmetic quotient intrinsically recognizes the
compactification kernel; that remains a separate geometric assertion.

The continuous
character descent supplier currently belongs to `AnabelianGeometry`.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory EtaleCohomology.Classical
open EtaleFundamentalGroups.Cohomology AnabelianGeometry.WeightFiltration

namespace AnabelianGeometry.FiniteField

/-- Actual compactification H¹ consists precisely of the characters annihilating
the kernel of the actual fundamental-group map. -/
theorem rationalH1_exists_compactificationPullback_iff_ker_le
    {X U : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral U] (j : U ⟶ X) [IsOpenImmersion j]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ U)
    (ℓ : ℕ) [Fact ℓ.Prime] (a : rationalEllAdicCohomology ℓ U 1) :
    (∃ b : rationalEllAdicCohomology ℓ X 1, rationalEllAdicPullback j ℓ 1 b = a) ↔
      (FiniteEtale.fundamentalGroupHom j ξ).toMonoidHom.ker ≤
        ((rationalEllAdicH1CharacterEquiv ξ ℓ a).toMul).toMonoidHom.ker := by
  have hq := FiniteEtale.fundamentalGroupHom_surjective_of_isOpenImmersion j ξ
  rw [← exists_continuousHom_factor_iff_ker_le
    (FiniteEtale.fundamentalGroupHom j ξ) hq (rationalEllAdicH1CharacterEquiv ξ ℓ a).toMul]
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨(rationalEllAdicH1CharacterEquiv (ξ ≫ j) ℓ b).toMul, ?_⟩
    exact (congrArg (fun χ : rationalPadicCharacters ξ ℓ => χ.toMul)
      (LinearMap.congr_fun (rationalEllAdicH1Character_schemePullback j ξ ℓ) b)).symm
  · rintro ⟨ψ, hψ⟩
    let b := (rationalEllAdicH1CharacterEquiv (ξ ≫ j) ℓ).symm (Additive.ofMul ψ)
    refine ⟨b, (rationalEllAdicH1CharacterEquiv ξ ℓ).injective ?_⟩
    have hn := LinearMap.congr_fun (rationalEllAdicH1Character_schemePullback j ξ ℓ) b
    change rationalEllAdicH1CharacterEquiv ξ ℓ (rationalEllAdicPullback j ℓ 1 b) =
      rationalCharacterSchemePullback j ξ ℓ
        (rationalEllAdicH1CharacterEquiv (ξ ≫ j) ℓ b) at hn
    have hb : rationalEllAdicH1CharacterEquiv (ξ ≫ j) ℓ b = Additive.ofMul ψ :=
      (rationalEllAdicH1CharacterEquiv (ξ ≫ j) ℓ).apply_symm_apply (Additive.ofMul ψ)
    rw [hb] at hn
    exact hn.trans (congrArg Additive.ofMul hψ)

end AnabelianGeometry.FiniteField
