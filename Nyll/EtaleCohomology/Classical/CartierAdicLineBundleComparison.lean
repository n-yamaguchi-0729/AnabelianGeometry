/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.CartierAdicCycleClass
public import Nyll.EtaleCohomology.Classical.CartierCycleAdditivity
public import Nyll.EtaleCohomology.Classical.CartierLineBundleComparison
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.SchemeTheory.Divisors.CartierProducts
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Original adic classes of isomorphic signed divisor bundles

The original roots comparison carries Cartier addition and the proved
geometric line-bundle comparison to each finite cyclic group. Projection
to every finite level gives the same equality in the original inverse
limit, and actual scalar extension gives it in rational cohomology.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped TensorProduct
open EtaleCohomology.Classical

namespace EtaleCohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X]
  (c : X ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- Multiplication of actual Cartier ideals adds their original finite
cycle classes. -/
theorem finiteEffectiveCartierCycleClass_mul
    (n : ℕ) (D E : Scheme.EffectiveCartierDivisor X) :
    finiteEffectiveCartierCycleClass c ℓ hℓ n ⟨D.1 * E.1, D.2.mul E.2⟩ =
      finiteEffectiveCartierCycleClass c ℓ hℓ n D +
        finiteEffectiveCartierCycleClass c ℓ hℓ n E := by
  let e := finiteLevelKummerCohomologyEquiv c ℓ hℓ n 2
  apply e.injective
  exact (finiteEffectiveCartierCycleClass_kummer c ℓ hℓ n
    ⟨D.1 * E.1, D.2.mul E.2⟩).trans
      ((effectiveCartierCycleClass_mul D E (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
        (etaleKummerExponentUnit_of_base c
          (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))).trans
        ((congrArg₂
          (fun a b : Sheaf.H.{u} (etaleRootsOfUnitySheaf X (ℓ ^ (n + 1))) 2 => a + b)
          (finiteEffectiveCartierCycleClass_kummer c ℓ hℓ n D).symm
          (finiteEffectiveCartierCycleClass_kummer c ℓ hℓ n E).symm).trans
          (e.map_add (finiteEffectiveCartierCycleClass c ℓ hℓ n D)
            (finiteEffectiveCartierCycleClass c ℓ hℓ n E)).symm))

/-- The actual integral Cartier family is additive under multiplication
of the original ideals. -/
theorem integralEffectiveCartierCycleClass_mul
    (D E : Scheme.EffectiveCartierDivisor X) :
    integralEffectiveCartierCycleClass c ℓ hℓ ⟨D.1 * E.1, D.2.mul E.2⟩ =
      integralEffectiveCartierCycleClass c ℓ hℓ D +
        integralEffectiveCartierCycleClass c ℓ hℓ E := by
  apply ellAdicCohomology_ext X ℓ 2
  intro n
  exact (integralEffectiveCartierCycleClass_projection c ℓ hℓ
    ⟨D.1 * E.1, D.2.mul E.2⟩ n).trans
      ((finiteEffectiveCartierCycleClass_mul c ℓ hℓ n D E).trans
        ((congrArg₂ (fun a b : finiteLevelCohomology X ℓ n 2 => a + b)
          (integralEffectiveCartierCycleClass_projection c ℓ hℓ D n).symm
          (integralEffectiveCartierCycleClass_projection c ℓ hℓ E n).symm).trans
          (map_add (ellAdicProjection X ℓ 2 n)
            (integralEffectiveCartierCycleClass c ℓ hℓ D)
            (integralEffectiveCartierCycleClass c ℓ hℓ E)).symm))

/-- Actual rational scalar extension retains Cartier addition. -/
theorem rationalEffectiveCartierCycleClass_mul
    (D E : Scheme.EffectiveCartierDivisor X) :
    rationalEffectiveCartierCycleClass c ℓ hℓ ⟨D.1 * E.1, D.2.mul E.2⟩ =
      rationalEffectiveCartierCycleClass c ℓ hℓ D +
        rationalEffectiveCartierCycleClass c ℓ hℓ E := by
  exact (congrArg (fun x : ellAdicCohomology X ℓ 2 => (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x)
    (integralEffectiveCartierCycleClass_mul c ℓ hℓ D E)).trans
      (TensorProduct.tmul_add (R := ℤ_[ℓ]) (1 : ℚ_[ℓ])
        (integralEffectiveCartierCycleClass c ℓ hℓ D)
        (integralEffectiveCartierCycleClass c ℓ hℓ E))

/-- An isomorphism of actual signed divisor bundles identifies their
signed original finite cycle classes. -/
theorem finiteEffectiveCartierCycleClass_sub_eq_of_lineBundleIso
    (n : ℕ) (D E A B : Scheme.EffectiveCartierDivisor X)
    (e : D.1.invModule ⊗ E.1.module ≅ A.1.invModule ⊗ B.1.module) :
    finiteEffectiveCartierCycleClass c ℓ hℓ n D -
        finiteEffectiveCartierCycleClass c ℓ hℓ n E =
      finiteEffectiveCartierCycleClass c ℓ hℓ n A -
        finiteEffectiveCartierCycleClass c ℓ hℓ n B := by
  apply (finiteLevelKummerCohomologyEquiv c ℓ hℓ n 2).injective
  simpa only [map_sub, finiteEffectiveCartierCycleClass_kummer] using
    effectiveCartierCycleClass_sub_eq_of_lineBundleIso D E A B e
      (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
      (etaleKummerExponentUnit_of_base c
        (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))

/-- The same geometric isomorphism gives equality of the signed
original integral inverse-limit classes. -/
theorem integralEffectiveCartierCycleClass_sub_eq_of_lineBundleIso
    (D E A B : Scheme.EffectiveCartierDivisor X)
    (e : D.1.invModule ⊗ E.1.module ≅ A.1.invModule ⊗ B.1.module) :
    integralEffectiveCartierCycleClass c ℓ hℓ D -
        integralEffectiveCartierCycleClass c ℓ hℓ E =
      integralEffectiveCartierCycleClass c ℓ hℓ A -
        integralEffectiveCartierCycleClass c ℓ hℓ B := by
  apply ellAdicCohomology_ext X ℓ 2
  intro n
  simp only [map_sub, integralEffectiveCartierCycleClass_projection]
  exact finiteEffectiveCartierCycleClass_sub_eq_of_lineBundleIso c ℓ hℓ n D E A B e

/-- The original rational cycle class of a divisor difference depends
only on its actual geometric line bundle. -/
theorem rationalEffectiveCartierCycleClass_sub_eq_of_lineBundleIso
    (D E A B : Scheme.EffectiveCartierDivisor X)
    (e : D.1.invModule ⊗ E.1.module ≅ A.1.invModule ⊗ B.1.module) :
    rationalEffectiveCartierCycleClass c ℓ hℓ D -
        rationalEffectiveCartierCycleClass c ℓ hℓ E =
      rationalEffectiveCartierCycleClass c ℓ hℓ A -
        rationalEffectiveCartierCycleClass c ℓ hℓ B := by
  exact (TensorProduct.tmul_sub (R := ℤ_[ℓ]) (1 : ℚ_[ℓ])
    (integralEffectiveCartierCycleClass c ℓ hℓ D)
    (integralEffectiveCartierCycleClass c ℓ hℓ E)).symm.trans
      ((congrArg (fun x : ellAdicCohomology X ℓ 2 => (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x)
        (integralEffectiveCartierCycleClass_sub_eq_of_lineBundleIso c ℓ hℓ D E A B e)).trans
        (TensorProduct.tmul_sub (R := ℤ_[ℓ]) (1 : ℚ_[ℓ])
          (integralEffectiveCartierCycleClass c ℓ hℓ A)
          (integralEffectiveCartierCycleClass c ℓ hℓ B)))

end EtaleCohomology
