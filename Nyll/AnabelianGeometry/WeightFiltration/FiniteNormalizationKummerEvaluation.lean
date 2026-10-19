/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.FiniteNormalizationRadicals
import Nyll.AnabelianGeometry.WeightFiltration.FiniteNormalizationLocalAmbient
import Nyll.AnabelianGeometry.WeightFiltration.FiniteNormalizationRadicalRatios
import Nyll.AnabelianGeometry.WeightFiltration.FiniteNormalizationRadicalValuation

/-!
# Actual Kummer ratios in finite local normalizations

A prescribed ambient radical is placed into an actual finite normalization.
Its local inertia coefficient maps to the original field Kummer ratio, and
its residue is evaluated by the original finite tame coordinate.
-/

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

universe u v w

/-- Realize and evaluate a prescribed ambient Kummer ratio
in an actual finite local normalization. -/
theorem exists_finiteNormalization_kummerEvaluation
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CharZero (IsLocalRing.ResidueField A)] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]
    (σ : actualNormalizationInertiaGroup A K L Q)
    (n : ℕ) (hn : 0 < n) (a : A) (β : L) (hβ : β ≠ 0)
    (hpow : β ^ n = algebraMap A L a) :
    ∃ E : FiniteGaloisIntermediateField K L,
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
      ∃ (x : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
        (m : ℕ) (c : (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))ˣ),
        finiteNormalizationLocalAmbient A K L Q E x = β ∧
        x ^ n = algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
          (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
          (algebraMap A (finiteAbsoluteNormalizationAlgebra A K L E) a) ∧
        IsDiscreteValuationRing.addVal _ x = m ∧
        n * m = (IsDiscreteValuationRing.addVal A a).toNat *
          (finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A ∧
        c ^ n = 1 ∧
        finiteNormalizationLocalAmbient A K L Q E c =
          galoisAutomorphismRingHom K L (actualNormalizationInertiaElement A K L Q σ) β / β ∧
        actualFiniteLocalResidueMap A K L Q E c =
          (((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val).val ^ m := by
  obtain ⟨E, b, hb, hbpow⟩ := exists_finiteNormalization_radical A K L n hn a β hpow
  refine ⟨E, ?_⟩
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
  let x := algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
    (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) b
  have hxb : finiteNormalizationLocalAmbient A K L Q E x = β :=
    (finiteNormalizationLocalAmbient_algebraMap A K L Q E b).trans hb
  have hx : x ≠ 0 := by
    intro hx
    apply hβ
    rw [← hxb, hx, map_zero]
  have hxpow : x ^ n = algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
      (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
      (algebraMap A (finiteAbsoluteNormalizationAlgebra A K L E) a) := by
    rw [← hbpow, map_pow]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  have hm := IsDiscreteValuationRing.addVal_def x u hπ m hu
  obtain ⟨c, hc, hcn, hres⟩ :=
    finiteNormalizationTame_radicalRatio_charZero A K L Q E σ x hx m hm n a hxpow
  have ha : a ≠ 0 := by
    intro ha
    have hz : β ^ n = 0 := by rw [hpow, ha, map_zero]
    exact (pow_ne_zero n hβ) hz
  have hv := finiteNormalizationRadical_value_relation A K L Q E a ha x n hxpow
  rw [hm, ENat.toNat_natCast] at hv
  refine ⟨x, m, c, hxb, hxpow, hm, hv, hcn, ?_, hres⟩
  have h := finiteNormalizationLocalAmbient_unitRatio A K L Q E σ x
    (by rw [hxb]; exact hβ) c hc
  simpa only [hxb] using h

end AnabelianGeometry.WeightFiltration
