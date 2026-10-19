/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.PrimePowerNormSum

/-! # Exact norm kernels for good prime-power principal units -/

namespace AnabelianGeometry.KummerTheory

/-- The norm kernel is the image of the generator minus one. -/
theorem geomSum_principalUnit_mul_eq_zero_iff
    {p : ℕ} (hp : p.Prime)
    (s : ℕ) (hs : s ≠ 0) (hps : s + 2 ≤ p * s)
    (a : ℤ) (ha : ¬ (p : ℤ) ∣ a)
    (k : ℕ) (t : ZMod (p ^ (k + s))) :
    ((∑ j ∈ Finset.range (p ^ k),
        (1 + (p : ZMod (p ^ (k + s))) ^ s * a) ^ j) * t = 0) ↔
      ∃ y : ZMod (p ^ (k + s)),
        ((1 + (p : ZMod (p ^ (k + s))) ^ s * a) - 1) * y = t := by
  let N : ℕ := p ^ (k + s)
  let U : ℤ := 1 + (p : ℤ) ^ s * a
  let S : ℤ := ∑ j ∈ Finset.range (p ^ k), U ^ j
  suffices hmain :
      (S : ZMod N) * t = 0 ↔
        ∃ y : ZMod N, ((U : ZMod N) - 1) * y = t by
    simpa only [S, U, N, Int.cast_sum, Int.cast_pow,
      Int.cast_add, Int.cast_one, Int.cast_mul, Int.cast_natCast] using hmain
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpa : IsCoprime (p : ℤ) a := hpZ.coprime_iff_not_dvd.mpr ha
  obtain ⟨b, hSb, hpb⟩ :=
    exists_geomSum_principalUnit_eq_primePow_mul hp s hs hps a ha k
  have hb : S = (p : ℤ) ^ k * b := hSb
  constructor
  · intro ht
    obtain ⟨T, rfl⟩ := ZMod.intCast_surjective t
    have hdiv : (N : ℤ) ∣ S * T :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (S * T) N).mp
        (by simpa only [Int.cast_mul] using ht)
    have hdiv' :
        (p : ℤ) ^ k * (p : ℤ) ^ s ∣ (p : ℤ) ^ k * (b * T) := by
      simpa only [N, Nat.cast_pow, Nat.cast_mul, pow_add, hb, mul_assoc] using hdiv
    have hbT : (p : ℤ) ^ s ∣ b * T :=
      (mul_dvd_mul_iff_left (pow_ne_zero k hpZ.ne_zero)).mp hdiv'
    have hcopb : IsCoprime ((p : ℤ) ^ s) b :=
      (hpZ.coprime_iff_not_dvd.mpr hpb).pow_left
    have hT : (p : ℤ) ^ s ∣ T := hcopb.dvd_of_dvd_mul_left hbT
    obtain ⟨c, hc⟩ := hT
    have hcopa : IsCoprime a (N : ℤ) := by
      simpa only [N, Nat.cast_pow] using
        (hpa.symm.pow_right : IsCoprime a ((p : ℤ) ^ (k + s)))
    obtain ⟨A, B, hAB⟩ := hcopa
    have hAB' : (A : ZMod N) * (a : ZMod N) = 1 := by
      have hcast := congrArg (fun z : ℤ => (z : ZMod N)) hAB
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast,
        ZMod.natCast_self, mul_zero, add_zero, Int.cast_one] using hcast
    refine ⟨((A * c : ℤ) : ZMod N), ?_⟩
    calc
      ((U : ZMod N) - 1) * ((A * c : ℤ) : ZMod N) =
          ((p : ZMod N) ^ s * (c : ZMod N)) *
            ((A : ZMod N) * (a : ZMod N)) := by
        dsimp [U]
        push_cast
        ring
      _ = (p : ZMod N) ^ s * (c : ZMod N) := by rw [hAB', mul_one]
      _ = (T : ZMod N) := by
        rw [hc]
        push_cast
        rfl
  · rintro ⟨y, hy⟩
    have hgeom : S * (U - 1) = U ^ (p ^ k) - 1 := geom_sum_mul U (p ^ k)
    have hdiv : (N : ℤ) ∣ U ^ (p ^ k) - 1 :=
      (primePow_dvd_principalUnit_pow_sub_one_iff
        hp s hs hps a ha k (p ^ k)).mpr dvd_rfl
    have hzero : ((U ^ (p ^ k) - 1 : ℤ) : ZMod N) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (U ^ (p ^ k) - 1) N).mpr hdiv
    rw [← hgeom] at hzero
    have hprod : (S : ZMod N) * ((U : ZMod N) - 1) = 0 := by
      simpa only [Int.cast_mul, Int.cast_sub, Int.cast_one] using hzero
    rw [← hy, ← mul_assoc, hprod, zero_mul]

end AnabelianGeometry.KummerTheory
