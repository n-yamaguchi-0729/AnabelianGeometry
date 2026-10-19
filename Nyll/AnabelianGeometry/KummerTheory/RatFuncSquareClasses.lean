/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # Rational-function square classes from all finite prime multiplicities -/

noncomputable section
open Polynomial UniqueFactorizationMonoid
open scoped BigOperators

namespace AnabelianGeometry.KummerTheory

variable {k : Type*} [Field k]

local instance : DecidableEq k := Classical.decEq k

/-- Even polynomial prime multiplicities give a constant times a square. -/
theorem polynomial_eq_constant_mul_sq_of_even_factors
    (f : k[X]) (hf : f ≠ 0)
    (h : ∀ P ∈ normalizedFactors f, 2 ∣ (normalizedFactors f).count P) :
    ∃ (c : kˣ) (q : k[X]), f = C (c : k) * q ^ 2 := by
  classical
  obtain ⟨m, hm⟩ := Multiset.exists_smul_of_dvd_count (normalizedFactors f) h
  have hassoc : Associated (m.prod ^ 2) f := by
    simpa only [hm, Multiset.prod_nsmul] using (prod_normalizedFactors hf)
  obtain ⟨v, hv⟩ := hassoc
  obtain ⟨c, hc, hcv⟩ := Polynomial.isUnit_iff.mp v.isUnit
  refine ⟨hc.unit, m.prod, ?_⟩
  rw [IsUnit.unit_spec, ← hv, ← hcv]
  ring

/-- Integer order at a normalized irreducible polynomial. -/
def rationalPrimeOrder (P : k[X]) (f : RatFunc k) : ℤ := by
  classical
  exact ((normalizedFactors f.num).count (normalize P) : ℤ) -
    ((normalizedFactors f.denom).count (normalize P) : ℤ)

/-- Parity at every finite prime determines the rational square class up to a constant. -/
theorem ratFunc_eq_constant_mul_sq_of_even_primeOrders
    (f : RatFunc k) (hf : f ≠ 0)
    (h : ∀ P : k[X], Irreducible P → (2 : ℤ) ∣ rationalPrimeOrder P f) :
    ∃ (c : kˣ) (s : RatFunc k), f = algebraMap k (RatFunc k) (c : k) * s ^ 2 := by
  classical
  have hdis : Disjoint (normalizedFactors f.num) (normalizedFactors f.denom) :=
    disjoint_normalizedFactors (RatFunc.isCoprime_num_denom f).isRelPrime
  have hn : ∀ P ∈ normalizedFactors f.num, 2 ∣ (normalizedFactors f.num).count P := by
    intro P hP
    have hnot : P ∉ normalizedFactors f.denom := by
      intro hPd
      exact (Multiset.disjoint_left.mp hdis) hP hPd
    have hp := h P (irreducible_of_normalized_factor P hP)
    simp only [rationalPrimeOrder, normalize_normalized_factor P hP,
      Multiset.count_eq_zero_of_notMem hnot, Int.natCast_zero, sub_zero] at hp
    exact_mod_cast hp
  have hd : ∀ P ∈ normalizedFactors f.denom, 2 ∣ (normalizedFactors f.denom).count P := by
    intro P hP
    have hnot : P ∉ normalizedFactors f.num := by
      intro hPn
      exact (Multiset.disjoint_left.mp hdis) hPn hP
    have hp := h P (irreducible_of_normalized_factor P hP)
    simp only [rationalPrimeOrder, normalize_normalized_factor P hP,
      Multiset.count_eq_zero_of_notMem hnot, Int.natCast_zero, zero_sub] at hp
    have hp' := dvd_neg.mp hp
    exact_mod_cast hp'
  obtain ⟨cn, qn, hnum⟩ := polynomial_eq_constant_mul_sq_of_even_factors
    f.num (RatFunc.num_ne_zero hf) hn
  obtain ⟨cd, qd, hden⟩ := polynomial_eq_constant_mul_sq_of_even_factors
    f.denom (RatFunc.denom_ne_zero f) hd
  have hC (c : k) : algebraMap k[X] (RatFunc k) (C c) = algebraMap k (RatFunc k) c :=
    (IsScalarTower.algebraMap_apply k k[X] (RatFunc k) c).symm
  refine ⟨cn / cd, algebraMap k[X] (RatFunc k) qn / algebraMap k[X] (RatFunc k) qd, ?_⟩
  calc
    f = algebraMap k[X] (RatFunc k) f.num / algebraMap k[X] (RatFunc k) f.denom :=
      (RatFunc.num_div_denom f).symm
    _ = algebraMap k (RatFunc k) ((cn / cd : kˣ) : k) *
        (algebraMap k[X] (RatFunc k) qn / algebraMap k[X] (RatFunc k) qd) ^ 2 := by
      rw [hnum, hden]
      simp only [map_mul, map_pow, hC, Units.val_div_eq_div_val, map_div₀, div_pow]
      exact (div_mul_div_comm _ _ _ _).symm

/-- Apply finite-prime parity to the quotient by the selected coordinate. -/
theorem ratFunc_eq_constant_mul_coordinate_mul_sq
    (f t : RatFunc k) (hf : f ≠ 0) (ht : t ≠ 0)
    (h : ∀ P : k[X], Irreducible P → (2 : ℤ) ∣ rationalPrimeOrder P (f / t)) :
    ∃ (c : kˣ) (s : RatFunc k), f = algebraMap k (RatFunc k) (c : k) * t * s ^ 2 := by
  obtain ⟨c, s, hs⟩ := ratFunc_eq_constant_mul_sq_of_even_primeOrders
    (f / t) (div_ne_zero hf ht) h
  refine ⟨c, s, ?_⟩
  calc
    f = (f / t) * t := (div_mul_cancel₀ f ht).symm
    _ = (algebraMap k (RatFunc k) (c : k) * s ^ 2) * t := by rw [hs]
    _ = algebraMap k (RatFunc k) (c : k) * t * s ^ 2 := by ring

end AnabelianGeometry.KummerTheory
