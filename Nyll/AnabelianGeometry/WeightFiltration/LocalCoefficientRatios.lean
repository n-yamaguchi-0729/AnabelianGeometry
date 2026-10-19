/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.InertiaUnitRatio

/-!
# Coefficient ratios through an actual residue map

This form uses the original local ring homomorphism and residue-field map,
so it applies directly to finite normalization maps without changing their
chosen group actions or residue fields.
-/

noncomputable section

namespace AnabelianGeometry.WeightFiltration

/-- A residue-fixed local action evaluates every unit ratio through a uniformizer ratio. -/
theorem localCoefficientRatio_residue
    {R k : Type*} [CommRing R] [IsDomain R] [Field k]
    (ρ : R →+* k) (σ : R →+* R) (hρ : ∀ z : R, ρ (σ z) = ρ z)
    (π : R) (hπ : π ≠ 0) (d : R) (hd : π * d = σ π)
    (x : R) (m : ℕ) (u c : Rˣ) (hx : x = π ^ m * (u : R))
    (hc : x * (c : R) = σ x) : ρ (c : R) = ρ d ^ m := by
  have he : (u : R) * (c : R) = d ^ m * σ (u : R) := by
    apply mul_left_cancel₀ (pow_ne_zero m hπ)
    calc
      π ^ m * ((u : R) * (c : R)) = x * (c : R) := by rw [hx, mul_assoc]
      _ = σ x := hc
      _ = σ π ^ m * σ (u : R) := by rw [hx, map_mul, map_pow]
      _ = (π * d) ^ m * σ (u : R) := by rw [hd]
      _ = π ^ m * (d ^ m * σ (u : R)) := by rw [mul_pow, mul_assoc]
  have hr := congrArg ρ he
  simp only [map_mul, map_pow, hρ] at hr
  apply mul_left_cancel₀ (Units.ne_zero (Units.map ρ.toMonoidHom u))
  exact hr.trans (mul_comm _ _)

/-- The ratio formula is expressed intrinsically using the normalized local valuation. -/
theorem localCoefficientRatio_residue_of_addVal
    {R k : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field k]
    (ρ : R →+* k) (σ : R →+* R) (hρ : ∀ z : R, ρ (σ z) = ρ z)
    (π : R) (hπ : Irreducible π) (d : R) (hd : π * d = σ π)
    (x : R) (hx : x ≠ 0) (m : ℕ) (hm : IsDiscreteValuationRing.addVal R x = m)
    (c : Rˣ) (hc : x * (c : R) = σ x) : ρ (c : R) = ρ d ^ m := by
  obtain ⟨r, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  have hrm := (IsDiscreteValuationRing.addVal_def x u hπ r hu).symm.trans hm
  have hr : r = m := by exact_mod_cast hrm
  subst r
  exact localCoefficientRatio_residue ρ σ hρ π hπ.ne_zero d hd x m u c
    (hu.trans (mul_comm _ _)) hc

end AnabelianGeometry.WeightFiltration
