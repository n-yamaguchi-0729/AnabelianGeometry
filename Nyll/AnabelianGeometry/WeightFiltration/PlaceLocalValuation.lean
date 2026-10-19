/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup

/-!
# Place orders and normalized local valuations

The divisor-theoretic order of a nonzero integral element agrees with the
normalized additive valuation of the place's DVR. Constants of characteristic
zero give a residue field of characteristic zero.
-/

noncomputable section

open AlgebraicCurve

namespace AnabelianGeometry.WeightFiltration

/-- Constants in characteristic zero force characteristic zero in a place residue field. -/
theorem place_residueField_charZero
    {k F : Type*} [Field k] [CharZero k] [Field F] [Algebra k F]
    (p : Place k F) : CharZero p.ResidueField := by
  constructor
  intro m n h
  have hc : (m : k) = (n : k) := (algebraMap k p.ResidueField).injective (by
    simpa only [map_natCast] using h)
  exact Nat.cast_injective hc

/-- The place order of a nonzero integral element is its normalized DVR valuation. -/
theorem place_ord_eq_addVal
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (p : Place k F) (a : p.toValuationSubring) (ha : a ≠ 0) :
    p.ord (a : F) = ((IsDiscreteValuationRing.addVal p.toValuationSubring a).toNat : ℤ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible p.toValuationSubring
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hm := IsDiscreteValuationRing.addVal_def a u hπ m hu
  calc
    p.ord (a : F) = (m : ℤ) := by
      rw [hu]
      change p.ord (((u : p.toValuationSubring) : F) * (π : F) ^ m) = (m : ℤ)
      simpa only [zpow_natCast] using p.ord_unit_smul_zpow u hπ (m : ℤ)
    _ = ((IsDiscreteValuationRing.addVal p.toValuationSubring a).toNat : ℤ) := by
      rw [hm, ENat.toNat_natCast]

end AnabelianGeometry.WeightFiltration
