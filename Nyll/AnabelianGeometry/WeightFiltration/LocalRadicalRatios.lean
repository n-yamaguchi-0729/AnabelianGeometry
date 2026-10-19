/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.LocalCoefficientRatios

/-!
# Unit ratios of local radicals

Uniformizer coefficients construct the unit ratio for every nonzero local
element. If a power of the element is fixed, this unit is a root of unity.
-/

noncomputable section

namespace AnabelianGeometry.WeightFiltration

/-- A unit uniformizer coefficient gives a unit coefficient on every nonzero element. -/
theorem localUnitRatio_exists
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (σ : R →+* R) (π : R) (hπ : Irreducible π)
    (d : Rˣ) (hd : π * (d : R) = σ π) (x : R) (hx : x ≠ 0) :
    ∃ c : Rˣ, x * (c : R) = σ x := by
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  refine ⟨d ^ m * Units.map σ.toMonoidHom u * u⁻¹, ?_⟩
  rw [hu, map_mul, map_pow, ← hd, mul_pow]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map]
  calc
    (u : R) * π ^ m * ((d : R) ^ m * σ (u : R) * ↑(u⁻¹)) =
        σ (u : R) * (π ^ m * (d : R) ^ m) * ((u : R) * ↑(u⁻¹)) := by ac_rfl
    _ = σ (u : R) * (π ^ m * (d : R) ^ m) := by rw [Units.mul_inv, mul_one]

/-- The unit ratio of an element whose nth power is fixed is an nth root of unity. -/
theorem localUnitRatio_pow_eq_one
    {R : Type*} [CommRing R] [IsDomain R] (σ : R →+* R)
    (x : R) (hx : x ≠ 0) (c : Rˣ) (hc : x * (c : R) = σ x)
    (n : ℕ) (hfixed : σ (x ^ n) = x ^ n) : c ^ n = 1 := by
  apply Units.ext
  change (c : R) ^ n = 1
  apply mul_left_cancel₀ (pow_ne_zero n hx)
  calc
    x ^ n * (c : R) ^ n = (x * (c : R)) ^ n := (mul_pow x (c : R) n).symm
    _ = σ (x ^ n) := by rw [hc, map_pow]
    _ = x ^ n := hfixed
    _ = x ^ n * 1 := (mul_one _).symm

end AnabelianGeometry.WeightFiltration
