/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.CartierCycleClass
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernelReduction
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Finite, integral, and rational Cartier cycle classes

Coherent primitive-root coordinates put the original Kummer cycle class in
the original finite cyclic cohomology. The actual Kummer exponent transitions
prove compatibility under the original finite reductions. This gives a class
in the original integral inverse limit and then its actual scalar extension
to rational ℓ-adic cohomology. No vanishing of surface H²(Gm) is used.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
open EtaleCohomology.Classical

namespace EtaleCohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X]
  (c : X ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- An effective Cartier divisor's actual Kummer class in the original
finite cyclic cohomology, using the existing coherent root coordinates. -/
def finiteEffectiveCartierCycleClass (n : ℕ) (D : Scheme.EffectiveCartierDivisor X) :
    finiteLevelCohomology X ℓ n 2 :=
  (finiteLevelKummerH1QuotientEquivH2Kernel c ℓ hℓ n
    (QuotientAddGroup.mk (effectiveCartierMultiplicativeGroupH1 D))).val

/-- The finite class retains the original roots-of-unity Kummer class. -/
theorem finiteEffectiveCartierCycleClass_kummer
    (n : ℕ) (D : Scheme.EffectiveCartierDivisor X) :
    finiteLevelKummerCohomologyEquiv c ℓ hℓ n 2
        (finiteEffectiveCartierCycleClass c ℓ hℓ n D) =
      effectiveCartierCycleClass D (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
        (etaleKummerExponentUnit_of_base c
          (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1))) := by
  rw [finiteEffectiveCartierCycleClass,
    finiteLevelKummerH1QuotientEquivH2Kernel_mk_val]
  exact (finiteLevelKummerCohomologyEquiv c ℓ hℓ n 2).apply_symm_apply _

/-- Original finite reduction preserves the same actual Cartier divisor.
Compatibility is proved from the actual Kummer short-complex transition. -/
theorem finiteEffectiveCartierCycleClass_reduction
    (n : ℕ) (D : Scheme.EffectiveCartierDivisor X) :
    finiteLevelReduction X ℓ n 2
        (finiteEffectiveCartierCycleClass c ℓ hℓ (n + 1) D) =
      finiteEffectiveCartierCycleClass c ℓ hℓ n D := by
  have h := congrArg Subtype.val
    (finiteLevelKummerH1QuotientEquivH2Kernel_reduction c ℓ hℓ n
      (QuotientAddGroup.mk (effectiveCartierMultiplicativeGroupH1 D)))
  rw [finiteLevelKummerH2KernelReduction_val,
    ellPowerKummerH1QuotientReduction_mk] at h
  exact h

/-- The finite class lies in the actual Kummer kernel inside the original
finite cohomology; the ambient H²(Gm) is not assumed to vanish. -/
theorem finiteEffectiveCartierCycleClass_toMultiplicativeGroup
    (n : ℕ) (D : Scheme.EffectiveCartierDivisor X) :
    finiteLevelH2ToMultiplicativeGroup c ℓ hℓ n
      (finiteEffectiveCartierCycleClass c ℓ hℓ n D) = 0 :=
  (finiteLevelKummerH1QuotientEquivH2Kernel c ℓ hℓ n
    (QuotientAddGroup.mk (effectiveCartierMultiplicativeGroupH1 D))).property

/-- The actual compatible family of the divisor's original finite cycle
classes, as an element of the original integral ℓ-adic cohomology. -/
def integralEffectiveCartierCycleClass (D : Scheme.EffectiveCartierDivisor X) :
    ellAdicCohomology X ℓ 2 :=
  ⟨fun n => finiteEffectiveCartierCycleClass c ℓ hℓ n D,
    fun n => finiteEffectiveCartierCycleClass_reduction c ℓ hℓ n D⟩

/-- Integral projection recovers the original finite cycle class. -/
theorem integralEffectiveCartierCycleClass_projection
    (D : Scheme.EffectiveCartierDivisor X) (n : ℕ) :
    ellAdicProjection X ℓ 2 n (integralEffectiveCartierCycleClass c ℓ hℓ D) =
      finiteEffectiveCartierCycleClass c ℓ hℓ n D := rfl

/-- The rational Cartier cycle class is the actual tensor of the original
integral class with `1` in ℚℓ. -/
def rationalEffectiveCartierCycleClass (D : Scheme.EffectiveCartierDivisor X) :
    rationalEllAdicCohomology ℓ X 2 :=
  (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] integralEffectiveCartierCycleClass c ℓ hℓ D

/-- The empty divisor is zero at every original finite level. -/
theorem finiteEffectiveCartierCycleClass_empty (n : ℕ) :
    finiteEffectiveCartierCycleClass c ℓ hℓ n
      (Scheme.EffectiveCartierDivisor.empty X) = 0 := by
  apply (finiteLevelKummerCohomologyEquiv c ℓ hℓ n 2).injective
  rw [finiteEffectiveCartierCycleClass_kummer, map_zero, effectiveCartierCycleClass_empty]

/-- The empty divisor is zero in the actual integral inverse limit. -/
theorem integralEffectiveCartierCycleClass_empty :
    integralEffectiveCartierCycleClass c ℓ hℓ
      (Scheme.EffectiveCartierDivisor.empty X) = 0 := by
  apply ellAdicCohomology_ext X ℓ 2
  intro n
  rw [integralEffectiveCartierCycleClass_projection, map_zero,
    finiteEffectiveCartierCycleClass_empty]

/-- The empty divisor is zero after the actual rational scalar extension. -/
theorem rationalEffectiveCartierCycleClass_empty :
    rationalEffectiveCartierCycleClass c ℓ hℓ
      (Scheme.EffectiveCartierDivisor.empty X) = 0 := by
  change ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] integralEffectiveCartierCycleClass c ℓ hℓ
    (Scheme.EffectiveCartierDivisor.empty X) :
      ℚ_[ℓ] ⊗[ℤ_[ℓ]] ellAdicCohomology X ℓ 2) = 0
  rw [integralEffectiveCartierCycleClass_empty, TensorProduct.tmul_zero]

end EtaleCohomology
