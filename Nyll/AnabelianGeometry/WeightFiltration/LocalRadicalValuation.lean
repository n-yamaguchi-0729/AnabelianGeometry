/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.LocalRamificationValuation

/-!
# Valuations of radicals in a prime localization

For an actual power equation over a DVR, the normalized order upstairs is
related to the base order by the literal ramification index.
-/

noncomputable section

namespace AnabelianGeometry.WeightFiltration

/-- A radical equation multiplies normalized orders by the actual ramification index. -/
theorem localRadical_value_relation
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [Algebra A B] [FaithfulSMul A B]
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal A)]
    [IsDiscreteValuationRing (Localization.AtPrime Q)]
    (a : A) (ha : a ≠ 0) (x : Localization.AtPrime Q) (n : ℕ)
    (hpow : x ^ n = algebraMap B (Localization.AtPrime Q) (algebraMap A B a)) :
    n * (IsDiscreteValuationRing.addVal (Localization.AtPrime Q) x).toNat =
      (IsDiscreteValuationRing.addVal A a).toNat * Q.ramificationIdx A := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπB : algebraMap A B π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    exact (FaithfulSMul.algebraMap_injective A B) (h.trans (map_zero _).symm)
  have himage : algebraMap B (Localization.AtPrime Q) (algebraMap A B π) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp
      (IsLocalization.nonZeroDivisors_le_comap Q.primeCompl (Localization.AtPrime Q)
        (mem_nonZeroDivisors_iff_ne_zero.mpr hπB))
  have hscale := localMap_addVal
    ((algebraMap B (Localization.AtPrime Q)).comp (algebraMap A B)) π hπ a ha
  have hs := congrArg ENat.toNat hscale
  change (IsDiscreteValuationRing.addVal (Localization.AtPrime Q)
      (algebraMap B (Localization.AtPrime Q) (algebraMap A B a))).toNat =
    (IsDiscreteValuationRing.addVal A a *
      IsDiscreteValuationRing.addVal (Localization.AtPrime Q)
        (algebraMap B (Localization.AtPrime Q) (algebraMap A B π))).toNat at hs
  rw [ENat.toNat_mul,
    localUniformizerValue_eq_ramificationIdx Q π hπ himage] at hs
  have hp := congrArg
    (fun z => (IsDiscreteValuationRing.addVal (Localization.AtPrime Q) z).toNat) hpow
  rw [IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul,
    ENat.toNat_mul, ENat.toNat_natCast] at hp
  exact hp.trans hs

end AnabelianGeometry.WeightFiltration
