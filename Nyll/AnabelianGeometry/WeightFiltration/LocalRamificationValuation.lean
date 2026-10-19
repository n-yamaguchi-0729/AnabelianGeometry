/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.LocalCoefficientRatios
import Nyll.EtaleFundamentalGroups.Inertia.UniformizerRadicalRamification

/-!
# Normalized valuations and ramification lengths

The length definition of ramification is compared with the normalized additive
valuation used to evaluate local inertia coefficients.
-/

noncomputable section

namespace AnabelianGeometry.WeightFiltration

/-- On nonzero elements of a DVR, length-theoretic order is normalized additive valuation. -/
theorem localOrder_eq_addVal
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (x : R) (hx : x ≠ 0) : Ring.ord R x = IsDiscreteValuationRing.addVal R x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  calc
    Ring.ord R x = (m : ℕ∞) := by
      rw [hu, Ring.ord_mul_of_isUnit_left u.isUnit,
        Ring.ord_pow (mem_nonZeroDivisors_iff_ne_zero.mpr hπ.ne_zero),
        Ring.ord_of_irreducible hπ, nsmul_eq_mul, mul_one]
    _ = IsDiscreteValuationRing.addVal R x :=
      (IsDiscreteValuationRing.addVal_def x u hπ m hu).symm

/-- The value of a base uniformizer is the literal ramification length. -/
theorem localUniformizerValue_eq_ramificationIdx
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A]
    [IsDiscreteValuationRing A] [Algebra A B]
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal A)]
    [IsDomain (Localization.AtPrime Q)] [IsDiscreteValuationRing (Localization.AtPrime Q)]
    (π : A) (hπ : Irreducible π)
    (himage : algebraMap B (Localization.AtPrime Q) (algebraMap A B π) ≠ 0) :
    (IsDiscreteValuationRing.addVal (Localization.AtPrime Q)
      (algebraMap B (Localization.AtPrime Q) (algebraMap A B π))).toNat =
        Q.ramificationIdx A := by
  rw [EtaleFundamentalGroups.Inertia.ramificationIdx_eq_ord_localized_uniformizer Q π hπ,
    localOrder_eq_addVal _ himage]

/-- A homomorphism between DVRs scales every nonzero value by the value of a uniformizer. -/
theorem localMap_addVal
    {A R : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (f : A →+* R) (π : A) (hπ : Irreducible π) (a : A) (ha : a ≠ 0) :
    IsDiscreteValuationRing.addVal R (f a) =
      IsDiscreteValuationRing.addVal A a * IsDiscreteValuationRing.addVal R (f π) := by
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  rw [IsDiscreteValuationRing.addVal_def a u hπ m hu, hu, map_mul, map_pow,
    IsDiscreteValuationRing.addVal_mul]
  have hunit : IsDiscreteValuationRing.addVal R (f (u : A)) = 0 :=
    IsDiscreteValuationRing.addVal_eq_zero_of_unit (Units.map f.toMonoidHom u)
  rw [hunit, zero_add, IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul]

end AnabelianGeometry.WeightFiltration
