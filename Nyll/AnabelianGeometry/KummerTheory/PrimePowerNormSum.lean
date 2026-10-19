/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.PrimePowerPrincipalUnits
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Exact integer norm sums for good prime-power principal units -/

namespace AnabelianGeometry.KummerTheory

/-- The geometric norm is exactly a prime power times a prime-to-p integer. -/
theorem exists_geomSum_principalUnit_eq_primePow_mul
    {p : ℕ} (hp : p.Prime)
    (s : ℕ) (hs : s ≠ 0) (hps : s + 2 ≤ p * s)
    (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) (k : ℕ) :
    ∃ b : ℤ,
      (∑ j ∈ Finset.range (p ^ k),
        (1 + (p : ℤ) ^ s * a) ^ j) =
          (p : ℤ) ^ k * b ∧
      ¬ (p : ℤ) ∣ b := by
  let U : ℤ := 1 + (p : ℤ) ^ s * a
  let S : ℤ := ∑ j ∈ Finset.range (p ^ k), U ^ j
  have hgeom :
      S * ((p : ℤ) ^ s * a) = U ^ (p ^ k) - 1 := by
    simpa [S, U] using geom_sum_mul U (p ^ k)
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpa : IsCoprime (p : ℤ) a := hpZ.coprime_iff_not_dvd.mpr ha
  have hpak : IsCoprime ((p : ℤ) ^ k) a := hpa.pow_left
  have hdiv :
      (↑(p ^ (k + s)) : ℤ) ∣ U ^ (p ^ k) - 1 :=
    (primePow_dvd_principalUnit_pow_sub_one_iff
      hp s hs hps a ha k (p ^ k)).mpr dvd_rfl
  have hdiv' :
      (p : ℤ) ^ (k + s) ∣ S * ((p : ℤ) ^ s * a) := by
    simpa only [Nat.cast_pow, ← hgeom] using hdiv
  have hdiv'' :
      (p : ℤ) ^ s * (p : ℤ) ^ k ∣
        (p : ℤ) ^ s * (S * a) := by
    simpa only [pow_add, mul_assoc, mul_comm, mul_left_comm] using hdiv'
  have hSa : (p : ℤ) ^ k ∣ S * a :=
    (mul_dvd_mul_iff_left (pow_ne_zero s hpZ.ne_zero)).mp hdiv''
  have hS : (p : ℤ) ^ k ∣ S := hpak.dvd_of_dvd_mul_right hSa
  obtain ⟨b, hb⟩ := hS
  refine ⟨b, ?_, ?_⟩
  · simpa only [S, U] using hb
  · intro hpb
    obtain ⟨c, hc⟩ := hpb
    have hhigh :
        (↑(p ^ ((k + 1) + s)) : ℤ) ∣ U ^ (p ^ k) - 1 := by
      refine ⟨c * a, ?_⟩
      rw [← hgeom, hb, hc]
      push_cast
      simp only [pow_add, pow_succ]
      ring
    have hbad : p ^ (k + 1) ∣ p ^ k :=
      (primePow_dvd_principalUnit_pow_sub_one_iff
        hp s hs hps a ha (k + 1) (p ^ k)).mp hhigh
    have hpos : 0 < p ^ k := pow_pos hp.pos k
    have hle : p ^ (k + 1) ≤ p ^ k := Nat.le_of_dvd hpos hbad
    rw [pow_succ] at hle
    nlinarith [hp.two_le]

end AnabelianGeometry.KummerTheory
