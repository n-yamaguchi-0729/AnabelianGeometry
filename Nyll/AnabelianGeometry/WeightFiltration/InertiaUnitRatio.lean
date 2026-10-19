/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCharacter

/-!
# Inertia ratios and orders of vanishing

If an inertia element multiplies a nonzero local element by a unit, the
residue of that unit is the uniformizer character raised to the order of
the element. The unit factor in a uniformizer decomposition disappears
because actual inertia fixes the residue field.
-/

noncomputable section

open IsLocalRing
open RamificationTheory.HilbertRamification.DiscreteValuationRing

namespace AnabelianGeometry.WeightFiltration

/-- The residue of an actual inertia ratio is the character to the local order. -/
theorem inertia_unitRatio_residue_of_uniformizer_decomposition
    (R G : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Group G] [MulSemiringAction G R]
    (π : R) (hπ : Irreducible π) (x : R) (m : ℕ) (u c : Rˣ)
    (hx : x = π ^ m * (u : R)) (σ : (maximalIdeal R).inertia G)
    (hc : x * (c : R) = (σ : G) • x) :
    Units.map (residue R).toMonoidHom c = (inertiaResidueCharacter R G σ) ^ m := by
  let q := uniformizerRatioUnit R G π hπ (σ : G)
  have he : (u : R) * (c : R) = (q : R) ^ m * ((σ : G) • (u : R)) := by
    apply mul_left_cancel₀ (pow_ne_zero m hπ.ne_zero)
    calc
      π ^ m * ((u : R) * (c : R)) = x * (c : R) := by rw [hx, mul_assoc]
      _ = (σ : G) • x := hc
      _ = ((σ : G) • π) ^ m * ((σ : G) • (u : R)) := by
        rw [hx, smul_mul']
        exact congrArg (fun z : R => z * ((σ : G) • (u : R)))
          (map_pow (MulSemiringAction.toRingHom G R (σ : G)) π m)
      _ = (π * (q : R)) ^ m * ((σ : G) • (u : R)) := by
        rw [uniformizerRatioUnit_spec]
      _ = π ^ m * ((q : R) ^ m * ((σ : G) • (u : R))) := by
        rw [mul_pow, mul_assoc]
  have hr := congrArg (residue R) he
  simp only [map_mul, map_pow, inertia_residue_fixed] at hr
  rw [inertiaResidueCharacter_eq_uniformizer R G π hπ]
  apply Units.ext
  change residue R (c : R) = (residue R (q : R)) ^ m
  apply mul_left_cancel₀ (Units.ne_zero (Units.map (residue R).toMonoidHom u))
  exact hr.trans (mul_comm _ _)

/-- The exponent is the actual normalized additive valuation of the local element. -/
theorem inertia_unitRatio_residue_of_addVal
    (R G : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Group G] [MulSemiringAction G R]
    (x : R) (hx : x ≠ 0) (m : ℕ) (hm : IsDiscreteValuationRing.addVal R x = m)
    (c : Rˣ) (σ : (maximalIdeal R).inertia G) (hc : x * (c : R) = (σ : G) • x) :
    Units.map (residue R).toMonoidHom c = (inertiaResidueCharacter R G σ) ^ m := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  have hkm := (IsDiscreteValuationRing.addVal_def x u hπ k hu).symm.trans hm
  have hk : k = m := by exact_mod_cast hkm
  subst k
  exact inertia_unitRatio_residue_of_uniformizer_decomposition R G π hπ x m u c
    (hu.trans (mul_comm _ _)) σ hc

/-- For a radical, its inertia ratio is determined by the valuation of the radicand. -/
theorem inertia_radicalRatio_residue
    (R G : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Group G] [MulSemiringAction G R]
    (x a : R) (hx : x ≠ 0) (n : ℕ) (hn : 0 < n) (hroot : x ^ n = a)
    (c : Rˣ) (σ : (maximalIdeal R).inertia G) (hc : x * (c : R) = (σ : G) • x) :
    Units.map (residue R).toMonoidHom c =
      (inertiaResidueCharacter R G σ) ^ ((IsDiscreteValuationRing.addVal R a).toNat / n) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  have hm : IsDiscreteValuationRing.addVal R x = m :=
    IsDiscreteValuationRing.addVal_def x u hπ m hu
  have ha : IsDiscreteValuationRing.addVal R a = ((n * m : ℕ) : ENat) := by
    rw [← hroot, IsDiscreteValuationRing.addVal_pow, hm, nsmul_eq_mul, Nat.cast_mul]
  rw [ha]
  change Units.map (residue R).toMonoidHom c =
    (inertiaResidueCharacter R G σ) ^ ((n * m) / n)
  rw [Nat.mul_div_cancel_left m hn]
  exact inertia_unitRatio_residue_of_addVal R G x hx m hm c σ hc

end AnabelianGeometry.WeightFiltration
