/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.PlaceLocalValuation
import Nyll.AnabelianGeometry.WeightFiltration.KummerTameResidue
import Nyll.AlgebraicCurves.Places.Basic

/-!
# Actual tame values at arbitrary places

The integral Kummer residue formula extends to signed place orders by inversion.
This retains the value of each inertia character, including at poles.
-/

noncomputable section

open AlgebraicCurve SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

/-- The residue of the actual Kummer ratio is the tame coefficient to the signed place order. -/
theorem placeKummerRatio_residue_eq_tameCoefficient_zpow
    (k F L : Type*) [Field k] [CharZero k] [Field F] [Field L]
    [Algebra k F] [Algebra F L] [IsSepClosure F L]
    (p : Place k F) [Algebra p.toValuationSubring L]
    [IsScalarTower p.toValuationSubring F L]
    [Algebra k L] [IsScalarTower k p.toValuationSubring L]
    (Q : Ideal (normalizationCommAlgCat p.toValuationSubring L)) [Q.IsMaximal]
    (σ : actualNormalizationInertiaGroup p.toValuationSubring F L Q)
    (n : ℕ) (hn : 0 < n) (f : F) (hf : f ≠ 0)
    (β : L) (hβ : β ≠ 0) (hpow : β ^ n = algebraMap F L f)
    (δ : k)
    (hδ : algebraMap k L δ =
      galoisAutomorphismRingHom F L
        (actualNormalizationInertiaElement p.toValuationSubring F L Q σ) β / β) :
    let _ : CharZero p.ResidueField := place_residueField_charZero p
    let hnA := isUnit_natCast_of_residue_charZero p.toValuationSubring n (Nat.ne_of_gt hn)
    (normalizationBaseResidue p.toValuationSubring L Q).comp
        (algebraMap k p.toValuationSubring) δ =
      tameCoefficient p.toValuationSubring F L Q n hnA σ ^ p.ord f := by
  intro charZero hnA
  let ρ : k →+* Q.ResidueField :=
    (normalizationBaseResidue p.toValuationSubring L Q).comp
      (algebraMap k p.toValuationSubring)
  let s := galoisAutomorphismRingHom F L
    (actualNormalizationInertiaElement p.toValuationSubring F L Q σ)
  have hint (g : F) (hg : g ≠ 0) (hgA : g ∈ p.toValuationSubring)
      (b : L) (hb : b ≠ 0) (hbp : b ^ n = algebraMap F L g)
      (d : k) (hd : algebraMap k L d = s b / b) :
      ρ d = tameCoefficient p.toValuationSubring F L Q n hnA σ ^ p.ord g := by
    let a : p.toValuationSubring := ⟨g, hgA⟩
    have ha : a ≠ 0 := by
      intro h
      exact hg (congrArg (fun z : p.toValuationSubring => (z : F)) h)
    have hpa : b ^ n = algebraMap p.toValuationSubring L a :=
      hbp.trans (IsScalarTower.algebraMap_apply p.toValuationSubring F L a).symm
    have hdA : algebraMap p.toValuationSubring L
        (algebraMap k p.toValuationSubring d) = s b / b := by
      rw [← IsScalarTower.algebraMap_apply k p.toValuationSubring L]
      exact hd
    have h := kummerResidue_eq_tameCoefficient_pow p.toValuationSubring F L Q σ
      n hn a b hb hpa (algebraMap k p.toValuationSubring d) hdA
    change ρ d = _ at h
    rw [show p.ord g = _ from place_ord_eq_addVal p a ha, zpow_natCast]
    exact h
  by_cases hfA : f ∈ p.toValuationSubring
  · exact hint f hf hfA β hβ hpow δ hδ
  · have ho : p.ord f < 0 := lt_of_not_ge
      (fun h => hfA ((p.mem_iff_ord_nonneg hf).mpr h))
    have hi : f⁻¹ ∈ p.toValuationSubring := (p.mem_iff_ord_nonneg (inv_ne_zero hf)).mpr (by
      rw [p.ord_inv]
      exact neg_nonneg.mpr ho.le)
    have hpi : (β⁻¹) ^ n = algebraMap F L f⁻¹ := by
      rw [inv_pow, hpow, map_inv₀]
    have hdi : algebraMap k L δ⁻¹ = s (β⁻¹) / β⁻¹ := by
      rw [map_inv₀, hδ, map_inv₀, inv_div]
      simp only [s, div_eq_mul_inv, inv_inv, mul_comm]
    have h := hint f⁻¹ (inv_ne_zero hf) hi β⁻¹ (inv_ne_zero hβ) hpi δ⁻¹ hdi
    simpa only [map_inv₀, p.ord_inv, zpow_neg, inv_inv] using congrArg Inv.inv h

end AnabelianGeometry.WeightFiltration
