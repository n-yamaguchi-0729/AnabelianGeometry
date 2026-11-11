/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# Finite fixed fields of positive Frobenius powers

The actual arithmetic Frobenius power has finitely many fixed values, as
they are roots of the nonzero polynomial `X^(q^n) - X`.

-/

@[expose] public section

namespace FiniteField

/-- Every positive arithmetic Frobenius power has finitely many fixed
values in an algebraic extension of a finite field. -/
theorem finite_fixed_frobenius_pow
    (k Ω : Type*) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] (n : ℕ) (hn : n ≠ 0) :
    Finite {x : Ω // (frobeniusAlgEquivOfAlgebraic k Ω ^ n) x = x} := by
  have hpow (x : Ω) : (frobeniusAlgEquivOfAlgebraic k Ω ^ n) x =
      x ^ Fintype.card k ^ n := by
    rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate]
  have hS : {x : Ω | (frobeniusAlgEquivOfAlgebraic k Ω ^ n) x = x} =
      {x | Polynomial.IsRoot
        (Polynomial.X ^ (Fintype.card k ^ n) - Polynomial.X : Polynomial Ω) x} := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hpow]
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, sub_eq_zero]
  have hfinite : Set.Finite {x : Ω | (frobeniusAlgEquivOfAlgebraic k Ω ^ n) x = x} := by
    rw [hS]
    exact Polynomial.finite_setOfPred_isRoot
      (X_pow_card_sub_X_ne_zero Ω (one_lt_pow₀ Fintype.one_lt_card hn))
  exact hfinite.to_subtype

end FiniteField
