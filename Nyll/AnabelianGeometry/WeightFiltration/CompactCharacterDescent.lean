/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Separation.Hausdorff

/-!
# Continuous character descent through compact quotients

A continuous homomorphism descends through a continuous surjection from a
compact group to a Hausdorff group exactly when it kills the kernel.
-/

noncomputable section

namespace AnabelianGeometry.WeightFiltration

/-- Kernel containment is the exact criterion for continuous character descent. -/
theorem exists_continuousHom_factor_iff_ker_le
    {G H A : Type*} [Group G] [Group H] [Group A]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace A]
    [CompactSpace G] [T2Space H]
    (f : G →ₜ* H) (hf : Function.Surjective f) (χ : G →ₜ* A) :
    (∃ ψ : H →ₜ* A, ψ.comp f = χ) ↔ f.toMonoidHom.ker ≤ χ.toMonoidHom.ker := by
  constructor
  · rintro ⟨ψ, hψ⟩ g hg
    change f g = 1 at hg
    change χ g = 1
    have he := congrArg (fun q : G →ₜ* A => q g) hψ
    change ψ (f g) = χ g at he
    rw [← he, hg, map_one]
  · intro hker
    let ψ := f.toMonoidHom.liftOfSurjective hf ⟨χ.toMonoidHom, hker⟩
    have he (g : G) : ψ (f g) = χ g :=
      MonoidHom.liftOfRightInverse_comp_apply f.toMonoidHom (Function.surjInv hf)
        (Function.rightInverse_surjInv hf) ⟨χ.toMonoidHom, hker⟩ g
    have hq : Topology.IsQuotientMap (f : G → H) :=
      Topology.IsQuotientMap.of_surjective_continuous hf f.continuous
    have hcont : Continuous (ψ : H → A) := by
      apply hq.continuous_iff.mpr
      have heq : (ψ : H → A) ∘ (f : G → H) = χ := funext he
      rw [heq]
      exact χ.continuous
    refine ⟨⟨ψ, hcont⟩, ?_⟩
    apply ContinuousMonoidHom.ext
    exact he

/-- A descended continuous character is unique for a surjective quotient map. -/
theorem continuousHom_factor_unique
    {G H A : Type*} [Monoid G] [Monoid H] [Monoid A]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace A]
    (f : G →ₜ* H) (hf : Function.Surjective f) {ψ₁ ψ₂ : H →ₜ* A}
    (h : ψ₁.comp f = ψ₂.comp f) : ψ₁ = ψ₂ := by
  apply ContinuousMonoidHom.ext
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact congrArg (fun q : G →ₜ* A => q x) h

end AnabelianGeometry.WeightFiltration
