/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.IntrinsicBoundaryWeight
import Mathlib.Topology.Constructions

/-!
# Open restriction of the cyclotomic span

Restricting the acting group to an open subgroup does not alter the span.
This is the group-theoretic step for passing to a finite field extension;
comparison with actual geometric base change is a separate requirement.
-/

namespace AnabelianGeometry.WeightFiltration

/-- Restriction to an open acting subgroup leaves the intrinsic span unchanged. -/
theorem openCyclotomicSpan_restrict_openSubgroup
    {Γ R A : Type*}
    [Group Γ] [TopologicalSpace Γ] [Group R] [Group A]
    (a : Γ → R → R) (ρ : Γ → A → A)
    (H : OpenSubgroup Γ) :
    openCyclotomicSpan
        (fun σ : H => a σ.val)
        (fun σ : H => ρ σ.val) =
      openCyclotomicSpan a ρ := by
  unfold openCyclotomicSpan
  apply le_antisymm
  · apply iSup_le
    intro V
    apply iSup_le
    intro φ
    apply iSup_le
    intro hφ
    let V' : OpenSubgroup Γ :=
      { toSubgroup :=
          (V : Subgroup H).map (H : Subgroup Γ).subtype
        isOpen' := by
          change IsOpen ((Subtype.val : H → Γ) '' (V : Set H))
          exact H.isOpen.isOpenMap_subtype_val _ V.isOpen }
    have hφ' :
        ∀ σ ∈ V', ∀ t, φ (a σ t) = ρ σ (φ t) := by
      intro σ hσ t
      change ∃ s : H, s ∈ V ∧ (s : Γ) = σ at hσ
      obtain ⟨s, hs, rfl⟩ := hσ
      exact hφ s hs t
    exact le_iSup_of_le V'
      (le_iSup_of_le φ (le_iSup_of_le hφ' le_rfl))
  · apply iSup_le
    intro V
    apply iSup_le
    intro φ
    apply iSup_le
    intro hφ
    let V' : OpenSubgroup H :=
      V.comap (H : Subgroup Γ).subtype continuous_subtype_val
    have hφ' :
        ∀ σ : H, σ ∈ V' → ∀ t,
          φ (a σ.val t) = ρ σ.val (φ t) := by
      intro σ hσ t
      exact hφ σ.val hσ t
    exact le_iSup_of_le V'
      (le_iSup_of_le φ (le_iSup_of_le hφ' le_rfl))

end AnabelianGeometry.WeightFiltration
