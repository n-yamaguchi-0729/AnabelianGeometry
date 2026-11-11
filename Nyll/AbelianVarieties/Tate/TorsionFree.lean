/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Tate.PrimePower
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Torsion-freeness of compatible prime-power Tate sequences

Multiplication by the chosen prime is injective because every coordinate is
that prime times the next coordinate. The valuation factorization in the
p-adic integers then gives torsion-freeness without any finiteness, rank, or
divisibility assumption on the original point group.
-/

@[expose] public section

namespace TateModule

universe u

variable {p : ℕ} {M : Type u} [AddCommGroup M]

/-- A compatible prime-power sequence killed by its indexing prime is zero. -/
theorem eq_zero_of_prime_nsmul_eq_zero (x : TateModule p M) (h : p • x = 0) : x = 0 := by
  apply Subtype.ext
  funext n
  have hn := congrArg (fun z : TateModule p M => (z : ℕ → M) (n + 1)) h
  change p • (x : ℕ → M) (n + 1) = 0 at hn
  exact (compat x n).symm.trans ((natCast_zsmul ((x : ℕ → M) (n + 1)) p).trans hn)

variable [Fact p.Prime]

/-- A compatible sequence killed by a power of the p-adic prime is zero. -/
theorem eq_zero_of_prime_pow_smul_eq_zero (n : ℕ) (x : TateModule p M)
    (h : (p : ℤ_[p]) ^ n • x = 0) : x = 0 := by
  induction n generalizing x with
  | zero => simpa only [pow_zero, one_smul] using h
  | succ n ih =>
    rw [pow_succ, mul_smul] at h
    have hx : (p : ℤ_[p]) • x = 0 := ih _ h
    apply eq_zero_of_prime_nsmul_eq_zero x
    simpa only [Nat.cast_smul_eq_nsmul] using hx

/-- The integral prime-power Tate module is torsion-free over the p-adic integers. -/
instance instIsTorsionFree : Module.IsTorsionFree ℤ_[p] (TateModule p M) :=
  Module.IsTorsionFree.of_smul_eq_zero fun a x h => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      rw [PadicInt.unitCoeff_spec ha, mul_smul] at h
      exact eq_zero_of_prime_pow_smul_eq_zero a.valuation x
        ((PadicInt.unitCoeff ha).isUnit.smul_eq_zero.mp h)

end TateModule
