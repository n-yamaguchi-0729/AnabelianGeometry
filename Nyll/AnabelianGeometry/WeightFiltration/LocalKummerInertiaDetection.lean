/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.ConstantKummerRatios
import Nyll.AnabelianGeometry.WeightFiltration.KummerTameResidue
import Nyll.AnabelianGeometry.WeightFiltration.TameCoefficientDetection

/-!
# Detecting local Kummer ramification by valuation

When the constant field contains the relevant roots of unity, actual
normalization inertia fixes a prescribed radical exactly when its base
valuation is divisible by the exponent.
-/

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

universe u v w t

/-- Actual inertia fixes a radical exactly when its base order vanishes modulo the exponent. -/
theorem normalizationInertia_fixes_radical_iff_dvd
    (k : Type t) (A : Type u) (K : Type v) (L : Type w)
    [Field k] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CharZero (IsLocalRing.ResidueField A)] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsSepClosure K L]
    [Algebra k A] [Algebra k L] [IsScalarTower k A L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]
    (n : ℕ) (hn : 0 < n) (hroot : ∃ ζ : k, IsPrimitiveRoot ζ n)
    (a : A) (β : L) (hβ : β ≠ 0) (hpow : β ^ n = algebraMap A L a) :
    (∀ σ : actualNormalizationInertiaGroup A K L Q,
      galoisAutomorphismRingHom K L (actualNormalizationInertiaElement A K L Q σ) β = β) ↔
        n ∣ (IsDiscreteValuationRing.addVal A a).toNat := by
  let hnA : IsUnit (n : A) := isUnit_natCast_of_residue_charZero A n (Nat.ne_of_gt hn)
  let ρ : k →+* Q.ResidueField :=
    (normalizationBaseResidue A L Q).comp (algebraMap k A)
  have hiff (σ : actualNormalizationInertiaGroup A K L Q) :
      galoisAutomorphismRingHom K L (actualNormalizationInertiaElement A K L Q σ) β = β ↔
        tameCoefficient A K L Q n hnA σ ^ (IsDiscreteValuationRing.addVal A a).toNat = 1 := by
    let s := galoisAutomorphismRingHom K L (actualNormalizationInertiaElement A K L Q σ)
    have hfixed : s (β ^ n) = β ^ n := by
      rw [hpow]
      exact (AlgEquiv.restrictScalars A (actualNormalizationInertiaElement A K L Q σ)).commutes a
    obtain ⟨δ, hδ⟩ := exists_constant_kummerRatio n (Nat.ne_of_gt hn) hroot s β hβ hfixed
    have hδA : algebraMap A L (algebraMap k A (δ.val : k)) = s β / β := by
      rw [← IsScalarTower.algebraMap_apply k A L]
      exact hδ
    have hf := kummerResidue_eq_tameCoefficient_pow A K L Q σ n hn a β hβ hpow
      (algebraMap k A (δ.val : k)) hδA
    constructor
    · intro hs
      have hd : (δ.val : k) = 1 := by
        apply (algebraMap k L).injective
        exact hδ.trans (by rw [show s β = β from hs, div_self hβ, map_one])
      rw [← hf, hd, map_one, map_one]
    · intro ht
      have hd : (δ.val : k) = 1 := by
        apply ρ.injective
        exact (hf.trans ht).trans (map_one ρ).symm
      have hr : s β / β = 1 := hδ.symm.trans (by rw [hd, map_one])
      have he := congrArg (fun z : L => z * β) hr
      rw [div_mul_cancel₀ _ hβ, one_mul] at he
      exact he
  rw [← tameCoefficient_pow_trivial_iff_dvd A K L Q n hnA]
  exact ⟨fun h σ => (hiff σ).mp (h σ), fun h σ => (hiff σ).mpr (h σ)⟩

end AnabelianGeometry.WeightFiltration
