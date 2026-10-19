/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Exact prime-power divisibility for principal units

The hypotheses uniformly cover odd primes and the 2-primary case with
principal units congruent to one modulo four. No Weil estimate is used.
-/

namespace AnabelianGeometry.KummerTheory

/-- Exact divisibility obtained from the finite principal-unit order formula. -/
theorem primePow_dvd_principalUnit_pow_sub_one_iff
    {p : ℕ} (hp : p.Prime)
    (s : ℕ) (hs : s ≠ 0) (hps : s + 2 ≤ p * s)
    (a : ℤ) (ha : ¬ (p : ℤ) ∣ a)
    (k d : ℕ) :
    (↑(p ^ (k + s)) : ℤ) ∣
        (1 + (p : ℤ) ^ s * a) ^ d - 1 ↔
      p ^ k ∣ d := by
  calc
    (↑(p ^ (k + s)) : ℤ) ∣
        (1 + (p : ℤ) ^ s * a) ^ d - 1 ↔
        (((1 + (p : ℤ) ^ s * a) ^ d - 1 : ℤ) :
          ZMod (p ^ (k + s))) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm
    _ ↔ (1 + (p : ZMod (p ^ (k + s))) ^ s * a) ^ d = 1 := by
      push_cast
      rw [sub_eq_zero]
    _ ↔ p ^ k ∣ d := by
      rw [← orderOf_dvd_iff_pow_eq_one,
        ZMod.orderOf_one_add_mul_prime_pow hp s hs hps a ha k]

end AnabelianGeometry.KummerTheory
