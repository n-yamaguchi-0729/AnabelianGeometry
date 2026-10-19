/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.FiniteNormalizationTameRatios
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameOrderTower

/-!
# Tame unit ratios in residue characteristic zero

In residue characteristic zero, the finite normalization exponent is one.
Consequently the original tame coordinate evaluates local unit ratios directly.
-/

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

universe u v w

/-- Nonzero natural numbers are units in a local ring of residue characteristic zero. -/
theorem isUnit_natCast_of_residue_charZero
    (A : Type u) [CommRing A] [IsLocalRing A]
    [CharZero (IsLocalRing.ResidueField A)] (n : ℕ) (hn : n ≠ 0) :
    IsUnit (n : A) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit (n : A)).mp
  rw [map_natCast]
  exact Nat.cast_ne_zero.mpr hn

/-- An integer coprime to all residue-invertible integers is one in residue characteristic zero. -/
theorem nat_eq_one_of_coprime_residue_units
    (A : Type u) [CommRing A] [IsLocalRing A]
    [CharZero (IsLocalRing.ResidueField A)] (d : ℕ)
    (h : ∀ n : ℕ, IsUnit (n : A) → Nat.Coprime n d) : d = 1 := by
  have hd : d ≠ 0 := by
    intro hd
    have hc := h 2 (isUnit_natCast_of_residue_charZero A 2 (by decide))
    rw [hd] at hc
    exact (by decide : ¬ Nat.Coprime 2 0) hc
  have hc := h d (isUnit_natCast_of_residue_charZero A d hd)
  change Nat.gcd d d = 1 at hc
  rwa [Nat.gcd_self] at hc

/-- The actual finite normalization has no wild normalization factor
in residue characteristic zero. -/
theorem finiteNormalization_exponent_eq_one
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CharZero (IsLocalRing.ResidueField A)] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L) :
    (finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A /
      actualFiniteStageTameOrder A K L Q E = 1 := by
  exact nat_eq_one_of_coprime_residue_units A _
    (actualFiniteStage_tame_arithmetic A K L Q E).2

/-- Actual tame coordinates evaluate local unit ratios without a wild exponent. -/
theorem finiteNormalizationTame_unitRatio_charZero
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CharZero (IsLocalRing.ResidueField A)] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    let : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
      finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    let : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E) :=
      finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
    let : IsDiscreteValuationRing
        (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) :=
      localizationAtPrime_isDiscreteValuationRing
        (finiteAbsoluteNormalizationAlgebra A K L E)
        (finiteAbsoluteNormalizationPrime A K L Q E)
        (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)
    ∀ (x : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)), x ≠ 0 →
      ∀ m : ℕ, IsDiscreteValuationRing.addVal _ x = m →
      ∀ c : (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))ˣ,
        x * (c : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) =
          actualFiniteInertiaLocalRingHom A K L Q E σ x →
        actualFiniteLocalResidueMap A K L Q E c =
          (((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val).val ^ m := by
  intro prime dedekind dvr x hx m hm c hc
  have h := finiteNormalizationTame_unitRatio A K L Q E σ x hx m hm c hc
  simpa only [finiteNormalization_exponent_eq_one A K L Q E, pow_one] using h

end AnabelianGeometry.WeightFiltration
