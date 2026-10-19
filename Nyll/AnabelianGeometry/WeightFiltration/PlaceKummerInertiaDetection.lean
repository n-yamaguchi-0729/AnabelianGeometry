/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.PlaceLocalValuation
import Nyll.AnabelianGeometry.WeightFiltration.LocalKummerInertiaDetection
import Nyll.AlgebraicCurves.Places.Basic

/-!
# Place-theoretic detection of Kummer inertia

Actual normalization inertia fixes a prescribed radical exactly when the
place order is divisible by its exponent. Inversion treats poles, so the
criterion applies to arbitrary nonzero rational functions.
-/

noncomputable section

open AlgebraicCurve SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

variable (k F L : Type*) [Field k] [CharZero k] [Field F] [Field L]
  [Algebra k F] [Algebra F L] [IsSepClosure F L]
  (p : Place k F) [Algebra p.toValuationSubring L]
  [IsScalarTower p.toValuationSubring F L]
  [Algebra k L] [IsScalarTower k p.toValuationSubring L]
  (Q : Ideal (normalizationCommAlgCat p.toValuationSubring L)) [Q.IsMaximal]

/-- The integral case of the place-order criterion for actual inertia. -/
theorem placeInertia_fixes_integral_radical_iff_dvd
    (n : ℕ) (hn : 0 < n) (hroot : ∃ ζ : k, IsPrimitiveRoot ζ n)
    (a : p.toValuationSubring) (ha : a ≠ 0) (β : L) (hβ : β ≠ 0)
    (hpow : β ^ n = algebraMap p.toValuationSubring L a) :
    (∀ σ : actualNormalizationInertiaGroup p.toValuationSubring F L Q,
      galoisAutomorphismRingHom F L
        (actualNormalizationInertiaElement p.toValuationSubring F L Q σ) β = β) ↔
      (n : ℤ) ∣ p.ord (a : F) := by
  let : CharZero p.ResidueField := place_residueField_charZero p
  rw [place_ord_eq_addVal p a ha, Int.natCast_dvd_natCast]
  exact normalizationInertia_fixes_radical_iff_dvd k p.toValuationSubring F L Q
    n hn hroot a β hβ hpow

/-- Actual inertia detects the place order of an arbitrary nonzero Kummer radicand. -/
theorem placeInertia_fixes_radical_iff_dvd
    (n : ℕ) (hn : 0 < n) (hroot : ∃ ζ : k, IsPrimitiveRoot ζ n)
    (f : F) (hf : f ≠ 0) (β : L) (hβ : β ≠ 0)
    (hpow : β ^ n = algebraMap F L f) :
    (∀ σ : actualNormalizationInertiaGroup p.toValuationSubring F L Q,
      galoisAutomorphismRingHom F L
        (actualNormalizationInertiaElement p.toValuationSubring F L Q σ) β = β) ↔
      (n : ℤ) ∣ p.ord f := by
  by_cases hfA : f ∈ p.toValuationSubring
  · let a : p.toValuationSubring := ⟨f, hfA⟩
    have ha : a ≠ 0 := by
      intro h
      exact hf (congrArg (fun z : p.toValuationSubring => (z : F)) h)
    have hpa : β ^ n = algebraMap p.toValuationSubring L a :=
      hpow.trans (IsScalarTower.algebraMap_apply p.toValuationSubring F L a).symm
    exact placeInertia_fixes_integral_radical_iff_dvd k F L p Q n hn hroot a ha β hβ hpa
  · have ho : p.ord f < 0 := lt_of_not_ge
      (fun h => hfA ((p.mem_iff_ord_nonneg hf).mpr h))
    have hi : f⁻¹ ∈ p.toValuationSubring := (p.mem_iff_ord_nonneg (inv_ne_zero hf)).mpr (by
      rw [p.ord_inv]
      exact neg_nonneg.mpr ho.le)
    let a : p.toValuationSubring := ⟨f⁻¹, hi⟩
    have ha : a ≠ 0 := by
      intro h
      exact (inv_ne_zero hf) (congrArg (fun z : p.toValuationSubring => (z : F)) h)
    have hpa : (β⁻¹) ^ n = algebraMap p.toValuationSubring L a := by
      rw [inv_pow, hpow, ← map_inv₀]
      exact (IsScalarTower.algebraMap_apply p.toValuationSubring F L a).symm
    have h := placeInertia_fixes_integral_radical_iff_dvd k F L p Q n hn hroot a ha
      β⁻¹ (inv_ne_zero hβ) hpa
    simpa only [a, map_inv₀, inv_inj, p.ord_inv, dvd_neg] using h

end AnabelianGeometry.WeightFiltration
