/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Descent of lifts by correcting a cocycle

A lift along an augmented complex descends through the augmentation once
its difference cocycle in the kernel has a primitive. This is the algebraic
correction step in the passage from Cech acyclicity to derived acyclicity.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex

universe u v

/-- Correcting the difference of a local lift by a primitive makes it
factor through the augmentation. -/
theorem exists_lift_of_cocycle_primitives
    {C : Type u} [Category.{v} C] [Abelian C]
    (K S : ShortComplex C) (hK : K.Exact) [Epi K.g]
    (hS : S.ShortExact) {A : C} (d : A ⟶ K.X₁) (hd : d ≫ K.f = 0)
    (hprimitive : ∀ z : K.X₁ ⟶ S.X₁, d ≫ z = 0 →
      ∃ b : K.X₂ ⟶ S.X₁, K.f ≫ b = z)
    (t : K.X₃ ⟶ S.X₃) (s : K.X₂ ⟶ S.X₂) (hs : s ≫ S.g = K.g ≫ t) :
    ∃ a : K.X₃ ⟶ S.X₂, a ≫ S.g = t := by
  have : Mono S.f := hS.mono_f
  have hzero : (K.f ≫ s) ≫ S.g = 0 := by
    rw [Category.assoc, hs, ← Category.assoc, K.zero, zero_comp]
  obtain ⟨z, hz⟩ := KernelFork.IsLimit.lift' hS.fIsKernel (K.f ≫ s) hzero
  change z ≫ S.f = K.f ≫ s at hz
  have hclosed : d ≫ z = 0 := by
    apply (cancel_mono S.f).mp
    rw [Category.assoc, hz, ← Category.assoc, hd, zero_comp, zero_comp]
  obtain ⟨b, hb⟩ := hprimitive z hclosed
  have hcorrected : K.f ≫ (s - b ≫ S.f) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc, hb, hz, sub_self]
  obtain ⟨a, ha⟩ := CokernelCofork.IsColimit.desc' hK.gIsCokernel
    (s - b ≫ S.f) hcorrected
  change K.g ≫ a = s - b ≫ S.f at ha
  refine ⟨a, ?_⟩
  apply (cancel_epi K.g).mp
  rw [← Category.assoc, ha, Preadditive.sub_comp, Category.assoc,
    S.zero, comp_zero, sub_zero, hs]

end CategoryTheory.ShortComplex
