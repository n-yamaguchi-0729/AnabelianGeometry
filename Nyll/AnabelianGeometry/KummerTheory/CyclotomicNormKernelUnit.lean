/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Ring.GeomSum

/-! # The invertible-difference case of the cyclotomic norm kernel -/

namespace AnabelianGeometry.KummerTheory

/-- If the generator minus one is a unit, the cyclic norm kernel is its image. -/
theorem geomSum_mul_eq_zero_iff_of_isUnit_sub_one
    {R : Type*} [CommRing R] (u : R) (d : ℕ)
    (hu : u ^ d = 1) (hunit : IsUnit (u - 1)) (t : R) :
    (∑ j ∈ Finset.range d, u ^ j) * t = 0 ↔
      ∃ y : R, (u - 1) * y = t := by
  obtain ⟨v, hv⟩ := hunit
  let S : R := ∑ j ∈ Finset.range d, u ^ j
  have hgeom : S * (u - 1) = 0 := by
    dsimp [S]
    rw [geom_sum_mul, hu, sub_self]
  have hzero : S = 0 := by
    calc
      S = (S * (u - 1)) * (↑(v⁻¹) : R) := by simp [← hv, mul_assoc]
      _ = 0 := by rw [hgeom, zero_mul]
  constructor
  · intro _
    refine ⟨(↑(v⁻¹) : R) * t, ?_⟩
    simp [← hv, ← mul_assoc]
  · intro _
    change S * t = 0
    rw [hzero, zero_mul]

end AnabelianGeometry.KummerTheory
