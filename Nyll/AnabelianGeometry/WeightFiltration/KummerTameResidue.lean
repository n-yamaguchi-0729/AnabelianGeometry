/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.FiniteNormalizationKummerResidues
import Nyll.AnabelianGeometry.WeightFiltration.TameCoefficientReduction

/-!
# Kummer residues as powers of the original tame coefficient

In residue characteristic zero the field-theoretic Kummer ratio is the tame
coefficient raised to the base valuation. The formula uses the prescribed
ambient root and the original inertia action, independently of finite stages.
-/

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

universe u v w

/-- A compatible exponent equation can be reduced at any common multiple. -/
theorem scaledExponent_eq_div_mul
    {n e t m v : ℕ} (hn : 0 < n) (het : e ∣ t) (hnt : n ∣ t)
    (hv : n * m = v * e) : (t / e) * m = (t / n) * v := by
  apply Nat.eq_of_mul_eq_mul_left hn
  calc
    n * ((t / e) * m) = (t / e) * (n * m) := by ac_rfl
    _ = (t / e) * (v * e) := by rw [hv]
    _ = v * ((t / e) * e) := by ac_rfl
    _ = v * t := by rw [Nat.div_mul_cancel het]
    _ = ((t / n) * n) * v := by rw [Nat.div_mul_cancel hnt, mul_comm]
    _ = n * ((t / n) * v) := by ac_rfl

/-- In residue characteristic zero the actual ramification index equals the actual tame order. -/
theorem finiteNormalization_ramificationIdx_eq_tameOrder
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CharZero (IsLocalRing.ResidueField A)] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L) :
    (finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A =
      actualFiniteStageTameOrder A K L Q E := by
  have h := Nat.div_mul_cancel (actualFiniteStage_tame_arithmetic A K L Q E).1
  rw [finiteNormalization_exponent_eq_one A K L Q E, one_mul] at h
  exact h.symm

/-- The actual field Kummer ratio has residue equal to the tame coefficient to the base order. -/
theorem kummerResidue_eq_tameCoefficient_pow
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CharZero (IsLocalRing.ResidueField A)] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsSepClosure K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]
    (σ : actualNormalizationInertiaGroup A K L Q)
    (n : ℕ) (hn : 0 < n) (a : A) (β : L) (hβ : β ≠ 0)
    (hpow : β ^ n = algebraMap A L a) (δ : A)
    (hδ : algebraMap A L δ =
      galoisAutomorphismRingHom K L (actualNormalizationInertiaElement A K L Q σ) β / β) :
    normalizationBaseResidue A L Q δ =
      tameCoefficient A K L Q n
        (isUnit_natCast_of_residue_charZero A n (Nat.ne_of_gt hn)) σ ^
          (IsDiscreteValuationRing.addVal A a).toNat := by
  let hnA : IsUnit (n : A) := isUnit_natCast_of_residue_charZero A n (Nat.ne_of_gt hn)
  obtain ⟨E, m, hval, hres⟩ :=
    exists_finiteNormalization_kummerResidue A K L Q σ n hn a β hβ hpow δ hδ
  rw [finiteNormalization_ramificationIdx_eq_tameOrder A K L Q E] at hval
  obtain ⟨F, hF⟩ := exists_actualFiniteStageTameOrder_multiple A K L Q n hnA
  let T : FiniteGaloisIntermediateField K L := E ⊔ F
  have hET : actualFiniteStageTameOrder A K L Q E ∣ actualFiniteStageTameOrder A K L Q T :=
    actualFiniteStageTameOrder_dvd_of_le A K L Q E T le_sup_left
  have hnT : n ∣ actualFiniteStageTameOrder A K L Q T :=
    hF.trans (actualFiniteStageTameOrder_dvd_of_le A K L Q F T le_sup_right)
  have hm := scaledExponent_eq_div_mul hn hET hnT hval
  rw [tameCoefficient_eq_finite A K L Q n hnA T hnT σ, ← pow_mul]
  rw [actualFiniteTameCoordinate_tower A K L Q E T le_sup_left σ, ← pow_mul, hm] at hres
  exact hres

end AnabelianGeometry.WeightFiltration
