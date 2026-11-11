/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.CartierAdicCycleClass
public import Nyll.EtaleCohomology.Classical.CartierCyclePullback
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernelPullback
public import Nyll.EtaleCohomology.Classical.KummerH2Functoriality
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Original finite and ℓ-adic Cartier cycle classes under pullback

The genuine pullback theorem for original Cartier H¹(Gm) classes and
the existing coherent Kummer comparisons give naturality in the
original finite cyclic cohomology. Passing to the actual compatible
families and their actual rational tensors preserves that naturality.
No vanishing of ambient surface cohomology is assumed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
open EtaleCohomology.Classical

namespace EtaleCohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : Y ⟶ X) (c : X ⟶ Spec (.of K))
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- Actual finite coefficient pullback preserves the original Cartier
cycle class of the actual inverse-image ideal. -/
theorem finiteEffectiveCartierCycleClass_pullback
    (n : ℕ) (D : Scheme.EffectiveCartierDivisor X)
    (hD : (D.1.comap f).IsEffectiveCartier) :
    finiteLevelCohomologyPullback ℓ f n 2
        (finiteEffectiveCartierCycleClass c ℓ hℓ n D) =
      finiteEffectiveCartierCycleClass (f ≫ c) ℓ hℓ n ⟨D.1.comap f, hD⟩ := by
  have h := congrArg Subtype.val
    (finiteLevelKummerH1QuotientEquivH2Kernel_pullback f c ℓ hℓ n
      (QuotientAddGroup.mk (effectiveCartierMultiplicativeGroupH1 D)))
  rw [finiteLevelKummerH2KernelPullback_val,
    etaleKummerH1QuotientPullback_mk,
    effectiveCartierMultiplicativeGroupH1_pullback f D hD] at h
  exact h

/-- Actual pullback of the original compatible finite family is the
integral cycle class of the actual pulled-back Cartier ideal. -/
theorem integralEffectiveCartierCycleClass_pullback
    (D : Scheme.EffectiveCartierDivisor X)
    (hD : (D.1.comap f).IsEffectiveCartier) :
    ellAdicCohomologyPullback ℓ f 2 (integralEffectiveCartierCycleClass c ℓ hℓ D) =
      integralEffectiveCartierCycleClass (f ≫ c) ℓ hℓ ⟨D.1.comap f, hD⟩ := by
  apply ellAdicCohomology_ext Y ℓ 2
  intro n
  exact (ellAdicProjection_pullback ℓ f 2 n
    (integralEffectiveCartierCycleClass c ℓ hℓ D)).trans
    ((congrArg (finiteLevelCohomologyPullback ℓ f n 2)
      (integralEffectiveCartierCycleClass_projection c ℓ hℓ D n)).trans
      ((finiteEffectiveCartierCycleClass_pullback f c ℓ hℓ n D hD).trans
        (integralEffectiveCartierCycleClass_projection (f ≫ c) ℓ hℓ
          (⟨D.1.comap f, hD⟩ : Scheme.EffectiveCartierDivisor Y) n).symm))

/-- Actual rational scalar extension retains the genuine Cartier
pullback equality in the original rational ℓ-adic groups. -/
theorem rationalEffectiveCartierCycleClass_pullback
    (D : Scheme.EffectiveCartierDivisor X)
    (hD : (D.1.comap f).IsEffectiveCartier) :
    rationalEllAdicCohomologyPullback ℓ f 2 (rationalEffectiveCartierCycleClass c ℓ hℓ D) =
      rationalEffectiveCartierCycleClass (f ≫ c) ℓ hℓ ⟨D.1.comap f, hD⟩ := by
  exact (rationalEllAdicCohomologyPullback_tmul ℓ f 2 1
    (integralEffectiveCartierCycleClass c ℓ hℓ D)).trans
    (congrArg (fun a : ellAdicCohomology Y ℓ 2 => (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] a)
      (integralEffectiveCartierCycleClass_pullback f c ℓ hℓ D hD))

end EtaleCohomology
