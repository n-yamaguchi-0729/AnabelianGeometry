/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Transport of continuous characters and their annihilators

A topological group equivalence preserving a subgroup transports its character
annihilator. The induced quotient equivalence also transports residue ranges.
-/

noncomputable section

namespace AnabelianGeometry.WeightFiltration

variable {A₁ A₂ T : Type*}
  [Group A₁] [Group A₂]
  [TopologicalSpace A₁] [TopologicalSpace A₂]
  [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T]

/-- Pullback of continuous characters along a topological group equivalence. -/
def characterPullback (e : A₁ ≃ₜ* A₂) :
    Additive (A₂ →ₜ* T) ≃+ Additive (A₁ →ₜ* T) where
  toFun χ := Additive.ofMul
    (χ.toMul.comp (ContinuousMonoidHom.toContinuousMonoidHom e))
  invFun χ := Additive.ofMul
    (χ.toMul.comp (ContinuousMonoidHom.toContinuousMonoidHom e.symm))
  left_inv χ := by
    apply ContinuousMonoidHom.ext
    intro a
    change χ.toMul (e (e.symm a)) = χ.toMul a
    rw [e.apply_symm_apply]
  right_inv χ := by
    apply ContinuousMonoidHom.ext
    intro a
    change χ.toMul (e.symm (e a)) = χ.toMul a
    rw [e.symm_apply_apply]
  map_add' χ ψ := by
    apply ContinuousMonoidHom.ext
    intro a
    rfl

/-- Continuous characters vanishing on a specified subgroup. -/
def characterAnnihilator
    {A : Type*} [Group A] [TopologicalSpace A]
    (W : Subgroup A) : AddSubgroup (Additive (A →ₜ* T)) where
  carrier := {χ | W ≤ χ.toMul.toMonoidHom.ker}
  zero_mem' := by
    intro a ha
    rfl
  add_mem' := by
    intro χ ψ hχ hψ a ha
    change χ.toMul a * ψ.toMul a = 1
    have hχa : χ.toMul a = 1 := hχ ha
    have hψa : ψ.toMul a = 1 := hψ ha
    rw [hχa, hψa, one_mul]
  neg_mem' := by
    intro χ hχ a ha
    change (χ.toMul a)⁻¹ = 1
    have hχa : χ.toMul a = 1 := hχ ha
    rw [hχa, inv_one]

theorem mem_characterAnnihilator_pullback_iff
    (e : A₁ ≃ₜ* A₂) (W₁ : Subgroup A₁) (W₂ : Subgroup A₂)
    (hW : W₁.map e.toMulEquiv.toMonoidHom = W₂)
    (χ : Additive (A₂ →ₜ* T)) :
    characterPullback e χ ∈ characterAnnihilator W₁ ↔
      χ ∈ characterAnnihilator W₂ := by
  change W₁ ≤
      (χ.toMul.comp
        (ContinuousMonoidHom.toContinuousMonoidHom e)).toMonoidHom.ker ↔
    W₂ ≤ χ.toMul.toMonoidHom.ker
  rw [← hW]
  constructor
  · intro h b hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact h ha
  · intro h a ha
    exact h ⟨a, ha, rfl⟩

theorem characterAnnihilator_map_pullback
    (e : A₁ ≃ₜ* A₂) (W₁ : Subgroup A₁) (W₂ : Subgroup A₂)
    (hW : W₁.map e.toMulEquiv.toMonoidHom = W₂) :
    (characterAnnihilator (T := T) W₂).map
        (characterPullback e).toAddMonoidHom =
      characterAnnihilator W₁ := by
  ext χ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    exact (mem_characterAnnihilator_pullback_iff e W₁ W₂ hW ψ).mpr hψ
  · intro hχ
    refine ⟨(characterPullback e).symm χ, ?_, (characterPullback e).apply_symm_apply χ⟩
    apply (mem_characterAnnihilator_pullback_iff e W₁ W₂ hW _).mp
    simpa only [AddEquiv.apply_symm_apply] using hχ

/-- Boundary-preserving equivalences identify the corresponding annihilators. -/
def characterAnnihilatorEquiv
    (e : A₁ ≃ₜ* A₂) (W₁ : Subgroup A₁) (W₂ : Subgroup A₂)
    (hW : W₁.map e.toMulEquiv.toMonoidHom = W₂) :
    characterAnnihilator (T := T) W₂ ≃+
      characterAnnihilator (T := T) W₁ :=
  ((characterPullback e).addSubgroupMap
    (characterAnnihilator W₂)).trans
      (AddEquiv.addSubgroupCongr
        (characterAnnihilator_map_pullback e W₁ W₂ hW))

end AnabelianGeometry.WeightFiltration
