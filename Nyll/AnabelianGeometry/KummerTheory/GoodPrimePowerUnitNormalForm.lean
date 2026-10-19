/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic

/-! # Good prime-power units and their exact principal-unit normal form -/

namespace AnabelianGeometry.KummerTheory

/-- Positive integer representatives have the exact normal form needed for norms. -/
theorem goodPrimePowerRepresentative_normalForm
    {p r U : ℕ} (hp : p.Prime)
    (hUpos : 0 < U) (hUbound : U < p ^ r)
    (hgood : p = 2 → (4 : ℤ) ∣ (U : ℤ) - 1) :
    U = 1 ∨ ¬ p ∣ U - 1 ∨
      ∃ s a : ℕ, 0 < s ∧ s < r ∧ ¬ p ∣ a ∧
        U = 1 + p ^ s * a ∧ s + 2 ≤ p * s := by
  by_cases hUone : U = 1
  · exact Or.inl hUone
  right
  by_cases hdiv : p ∣ U - 1
  · right
    have hsub : U - 1 ≠ 0 := by omega
    obtain ⟨s, a, ha, hfac⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd hsub p hp.ne_one
    have hs : 0 < s := by
      apply Nat.pos_of_ne_zero
      intro hs0
      rw [hs0, pow_zero, one_mul] at hfac
      apply ha
      rwa [hfac] at hdiv
    have hapos : 0 < a := by
      apply Nat.pos_of_ne_zero
      intro ha0
      apply ha
      rw [ha0]
      exact dvd_zero p
    have hUeq : U = 1 + p ^ s * a := by omega
    have hpowle : p ^ s ≤ U - 1 := by
      rw [hfac]
      nlinarith [pow_pos hp.pos s]
    have hsr : s < r :=
      (Nat.pow_lt_pow_iff_right hp.one_lt).mp
        (lt_of_le_of_lt hpowle (by omega))
    have hps : s + 2 ≤ p * s := by
      by_cases hp2 : p = 2
      · have hs2 : 2 ≤ s := by
          by_contra hnot
          have hs1 : s = 1 := by omega
          have hfour := hgood hp2
          rw [hUeq] at hfour
          push_cast at hfour
          rw [hp2, hs1] at hfour
          norm_num at hfour
          have hfour' : (2 : ℤ) * 2 ∣ 2 * (a : ℤ) := by simpa using hfour
          have htwo : (2 : ℤ) ∣ (a : ℤ) :=
            (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp hfour'
          apply ha
          rw [hp2]
          exact_mod_cast htwo
        rw [hp2]
        omega
      · have hp3 : 3 ≤ p := by have := hp.two_le; omega
        nlinarith
    exact ⟨s, a, hs, hsr, ha, hUeq, hps⟩
  · exact Or.inl hdiv

/-- A good unit is trivial, has invertible difference, or has exact principal form. -/
theorem goodPrimePowerUnit_normalForm
    {p r : ℕ} (hp : p.Prime) (hr : 0 < r)
    (u : (ZMod (p ^ r))ˣ)
    (hgood : p = 2 → (4 : ℤ) ∣ (((u : ZMod (p ^ r)).val : ℤ) - 1)) :
    u = 1 ∨ IsUnit ((u : ZMod (p ^ r)) - 1) ∨
      ∃ (s : ℕ) (a : ℤ), 0 < s ∧ s < r ∧ ¬ (p : ℤ) ∣ a ∧
        (u : ZMod (p ^ r)) = 1 + (p : ZMod (p ^ r)) ^ s * a ∧
        s + 2 ≤ p * s := by
  let : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hmod : 1 < p ^ r := by
    simpa only [pow_zero] using (Nat.pow_lt_pow_iff_right hp.one_lt).mpr hr
  let : Fact (1 < p ^ r) := ⟨hmod⟩
  let U : ℕ := (u : ZMod (p ^ r)).val
  have hcastU : (U : ZMod (p ^ r)) = (u : ZMod (p ^ r)) :=
    ZMod.natCast_zmod_val _
  have hUpos : 0 < U := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hu0 : (u : ZMod (p ^ r)) = 0 := (ZMod.val_eq_zero _).mp hzero
    exact (Units.ne_zero u) hu0
  have hUbound : U < p ^ r := ZMod.val_lt _
  rcases goodPrimePowerRepresentative_normalForm hp hUpos hUbound hgood with
    hUone | hnot | hprincipal
  · left
    apply Units.ext
    rw [← hcastU, hUone]
    exact Nat.cast_one
  · right
    left
    have hUge : 1 ≤ U := hUpos
    have hnotZ : ¬ (p : ℤ) ∣ ((U - 1 : ℕ) : ℤ) := by exact_mod_cast hnot
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hcop : IsCoprime ((p : ℤ) ^ r) ((U - 1 : ℕ) : ℤ) :=
      (hpZ.coprime_iff_not_dvd.mpr hnotZ).pow_left
    have hcop' : IsCoprime ((p ^ r : ℕ) : ℤ) ((U - 1 : ℕ) : ℤ) := by
      simpa only [Nat.cast_pow] using hcop
    have hunit : IsUnit ((((U - 1 : ℕ) : ℤ)) : ZMod (p ^ r)) :=
      (ZMod.coe_int_isUnit_iff_isCoprime ((U - 1 : ℕ) : ℤ) (p ^ r)).mpr hcop'
    have hrepr : ((((U - 1 : ℕ) : ℤ)) : ZMod (p ^ r)) =
        (u : ZMod (p ^ r)) - 1 := by
      rw [Int.cast_natCast, Nat.cast_sub hUge, Nat.cast_one, hcastU]
    rwa [hrepr] at hunit
  · right
    right
    obtain ⟨s, a, hs, hsr, ha, hUeq, hps⟩ := hprincipal
    refine ⟨s, (a : ℤ), hs, hsr, ?_, ?_, hps⟩
    · exact_mod_cast ha
    · calc
        (u : ZMod (p ^ r)) = (U : ZMod (p ^ r)) := hcastU.symm
        _ = 1 + (p : ZMod (p ^ r)) ^ s * (a : ℤ) := by
          rw [hUeq]
          push_cast
          rfl

/-- Fixing fourth roots gives the representative's required congruence. -/
theorem four_dvd_val_sub_one_of_unitsMap_eq_one
    {N : ℕ} [NeZero N] (h4 : 4 ∣ N) (u : (ZMod N)ˣ)
    (hu : ZMod.unitsMap h4 u = 1) :
    (4 : ℤ) ∣ (((u : ZMod N).val : ℤ) - 1) := by
  let f : ZMod N →+* ZMod 4 := ZMod.castHom h4 (ZMod 4)
  have hfu : f (u : ZMod N) = 1 :=
    congrArg (fun v : (ZMod 4)ˣ => (v : ZMod 4)) hu
  have hval : ((((u : ZMod N).val : ℤ)) : ZMod 4) = 1 := by
    have h := congrArg f (ZMod.natCast_zmod_val (u : ZMod N))
    simpa only [map_natCast, Int.cast_natCast] using h.trans hfu
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (((u : ZMod N).val : ℤ) - 1) 4).mp
  rw [Int.cast_sub, Int.cast_one, hval, sub_self]

end AnabelianGeometry.KummerTheory
