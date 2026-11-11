/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Residue powers on roots of unity in normal local rings

Roots of nonzero order in the fraction field are integral, hence belong to
the normal local ring. Simple-root uniqueness proves injectivity of their
reduction whenever their order is a unit. Thus a compatible residue power
determines their actual field action without a valuation hypothesis.
-/

@[expose] public section

namespace SchemeTheory

/-- Compatible local and field automorphisms act by the same residue power
on every root of unity whose order is invertible in the normal local ring. -/
theorem cyclotomic_power_of_residue_power_of_normal_local
    (R L : Type*) [CommRing R] [IsLocalRing R] [IsIntegrallyClosed R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (τ : R ≃+* R) (σ : L ≃+* L)
    (hσ : ∀ a : R, σ (algebraMap R L a) = algebraMap R L (τ a))
    (q : ℕ) (hres : ∀ a : R,
      IsLocalRing.residue R (τ a) = IsLocalRing.residue R a ^ q)
    (n : ℕ) (hn : IsUnit (n : R)) (x : L) (hx : x ^ n = 1) : σ x = x ^ q := by
  have hn0 : n ≠ 0 := by
    intro hz
    rw [hz, Nat.cast_zero] at hn
    exact not_isUnit_zero hn
  have hint : IsIntegral R x := IsIntegral.of_pow (Nat.pos_of_ne_zero hn0)
    (hx.symm ▸ isIntegral_one)
  let a : R := IsIntegralClosure.mk' R x hint
  have ha : algebraMap R L a = x := IsIntegralClosure.algebraMap_mk' R x hint
  have hapow : a ^ n = 1 := by
    apply IsFractionRing.injective R L
    rw [map_pow, ha, hx, map_one]
  have hau : IsUnit a := (isUnit_pow_iff hn0).mp (hapow.symm ▸ isUnit_one)
  have hτpow : (τ a) ^ n = 1 := by rw [← map_pow, hapow, map_one]
  have hqpow : (a ^ q) ^ n = 1 := by rw [pow_right_comm, hapow, one_pow]
  let f : Polynomial R := Polynomial.X ^ n - 1
  have hτroot : f.eval (τ a) = 0 := by
    simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, hτpow, sub_self]
  have hqroot : f.eval (a ^ q) = 0 := by
    simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, hqpow, sub_self]
  have hdiff : ¬ IsUnit (τ a - a ^ q) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, map_pow, hres, sub_self]
    exact not_not_intro rfl
  have hder : IsUnit (f.derivative.eval (τ a)) := by
    simpa only [f, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_one, sub_zero, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] using hn.mul ((hau.map τ).pow (n - 1))
  have heq : τ a = a ^ q :=
    IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hτroot hqroot hdiff hder
  calc
    σ x = algebraMap R L (τ a) := ha ▸ hσ a
    _ = algebraMap R L (a ^ q) := congrArg (algebraMap R L) heq
    _ = x ^ q := (map_pow (algebraMap R L) a q).trans (congrArg (fun z : L => z ^ q) ha)

end SchemeTheory
