/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Double cosets for a specified surjective action

The representative g is sent to its original action on the chosen point.
The kernel and stabilizer-image identities supply the exact quotient relation.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

variable {G D X : Type*} [Group G] [Group D] [MulAction D X]
  [MulAction.IsPretransitive D X]

/-- A transitive action through the specified quotient is precisely the
double-coset space of its kernel and a subgroup mapping onto the stabilizer. -/
def doubleCosetEquivOfSurjectiveAction
    (ρ : G →* D) (hρ : Function.Surjective ρ)
    (N I : Subgroup G) (hN : N = ρ.ker)
    (w₀ : X) (hI : I.map ρ = MulAction.stabilizer D w₀) :
    DoubleCoset.Quotient (N : Set G) (I : Set G) ≃ X := by
  let φ : DoubleCoset.Quotient (N : Set G) (I : Set G) → X :=
    Quotient.lift (fun g : G => ρ g • w₀) (by
      intro a b hab
      obtain ⟨n, hn, i, hi, rfl⟩ := DoubleCoset.rel_iff.mp hab
      have hn' : ρ n = 1 := MonoidHom.mem_ker.mp (hN ▸ hn)
      have hi' : ρ i • w₀ = w₀ := by
        apply MulAction.mem_stabilizer_iff.mp
        rw [← hI]
        exact ⟨i, hi, rfl⟩
      simp [map_mul, mul_smul, hn', hi'])
  refine Equiv.ofBijective φ ⟨?_, ?_⟩
  · intro a b
    refine Quotient.inductionOn₂' a b ?_
    intro g h he
    change ρ g • w₀ = ρ h • w₀ at he
    have hgh : ρ (g⁻¹ * h) ∈ MulAction.stabilizer D w₀ := by
      rw [MulAction.mem_stabilizer_iff, map_mul, map_inv,
        mul_smul, ← he, inv_smul_smul]
    rw [← hI] at hgh
    obtain ⟨i, hi, hρi⟩ := hgh
    have hn : h * i⁻¹ * g⁻¹ ∈ N := by
      rw [hN, MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [hρi]
      simp [map_mul, map_inv]
    exact DoubleCoset.eq.mpr
      ⟨h * i⁻¹ * g⁻¹, hn, i, hi, by simp [mul_assoc]⟩
  · intro x
    obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D w₀ x
    obtain ⟨g, rfl⟩ := hρ d
    exact ⟨DoubleCoset.mk N I g, hd⟩

/-- The double-coset equivalence preserves the prescribed representative action. -/
@[simp] theorem doubleCosetEquivOfSurjectiveAction_mk
    (ρ : G →* D) (hρ : Function.Surjective ρ)
    (N I : Subgroup G) (hN : N = ρ.ker)
    (w₀ : X) (hI : I.map ρ = MulAction.stabilizer D w₀) (g : G) :
    doubleCosetEquivOfSurjectiveAction ρ hρ N I hN w₀ hI
      (DoubleCoset.mk N I g) = ρ g • w₀ := rfl

end EtaleFundamentalGroups.Inertia
