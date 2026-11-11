/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Scalar extension of two tensor factors

The canonical tensor interchange identifies the tensor of two scalar
extensions with the scalar extension of their tensor. Over a fraction
field, every tensor therefore has one nonzero common denominator in
the original tensor module.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace TensorProduct

variable (R A M N : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The original tensor maps to the tensor of its two scalar extensions. -/
def baseChangeTensorMap :
    (M ⊗[R] N) →ₗ[R] (A ⊗[R] M) ⊗[A] (A ⊗[R] N) :=
  ((AlgebraTensorModule.distribBaseChange R A M N).toLinearMap.restrictScalars R).comp
    (TensorProduct.mk R A (M ⊗[R] N) 1)

/-- The canonical map retains both original pure tensor factors. -/
theorem baseChangeTensorMap_tmul (m : M) (n : N) :
    baseChangeTensorMap R A M N (m ⊗ₜ[R] n) =
      (1 ⊗ₜ[R] m) ⊗ₜ[A] (1 ⊗ₜ[R] n) := rfl

/-- A tensor over the fraction field becomes the image of an original
tensor after multiplication by one nonzero original scalar. -/
theorem exists_nonzero_smul_eq_baseChangeTensorMap [IsDomain R]
    [IsFractionRing R A]
    (t : (A ⊗[R] M) ⊗[A] (A ⊗[R] N)) :
    ∃ (c : R) (_ : c ≠ 0) (s : M ⊗[R] N),
      baseChangeTensorMap R A M N s = algebraMap R A c • t := by
  let e := (AlgebraTensorModule.distribBaseChange R A M N).symm
  obtain ⟨⟨s, c⟩, hc⟩ := IsLocalizedModule.surj (nonZeroDivisors R)
    (TensorProduct.mk R A (M ⊗[R] N) 1) (e t)
  refine ⟨c, mem_nonZeroDivisors_iff_ne_zero.mp c.2, s, ?_⟩
  apply e.injective
  change e (e.symm (1 ⊗ₜ[R] s)) = e (algebraMap R A (c : R) • t)
  rw [e.apply_symm_apply, map_smul]
  simpa only [TensorProduct.mk_apply, Submonoid.smul_def, algebraMap_smul] using hc.symm

end TensorProduct
