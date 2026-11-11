/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FunctionField.MinimalPencils
public import Nyll.AlgebraicCurves.Places.Evaluation.Value
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-! # Normalize two distinct values of a minimal pencil -/

@[expose] public section

noncomputable section

open AlgebraicCurve
open scoped IntermediateField

namespace AnabelianGeometry.FunctionField

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]

/-- A minimal function with zero at one point and a distinct finite value at
another generates a pencil with zero and infinity at those same points. -/
theorem exists_normalized_minimal_of_zero_and_nonzero_value
    (hC : ConstantsAreBase K F) {x : F} (hx : IsMinimal (K := K) x)
    (P Q : Place K F) (hP : P.HasValue x 0)
    (c : K) (hc : c ≠ 0) (hQ : Q.HasValue x c) :
    ∃ z : F, IsMinimal (K := K) z ∧ P.HasValue z 0 ∧
      Q.HasValue z⁻¹ 0 ∧ x ∈ K⟮z⟯ := by
  have hxc := hx.not_constant hC
  let a : F := algebraMap K F c
  have ha : a ≠ 0 := (map_ne_zero (algebraMap K F)).mpr hc
  let u : F := x - a
  have hu : u ≠ 0 := by
    intro h
    apply hxc
    exact ⟨c, (sub_eq_zero.mp h).symm⟩
  have humin : IsMinimal (K := K) u := by
    simpa only [map_one, one_mul, map_neg, ← sub_eq_add_neg] using
      hx.affine hC 1 (-c) one_ne_zero
  let z : F := a * u⁻¹ + 1
  have hzmin : IsMinimal (K := K) z := by
    simpa only [map_one] using (humin.inv hC).affine hC c 1 hc
  have hzu : z * u = x := by
    change (a * u⁻¹ + 1) * u = x
    rw [add_mul, mul_assoc, inv_mul_cancel₀ hu, mul_one, one_mul]
    dsimp [u]
    ring
  have hzexpr : z = x / u := (eq_div_iff hu).mpr hzu
  have hzP : P.HasValue z 0 := by
    have huP : P.HasValue u (-c) := by
      simpa only [zero_sub] using hP.sub (P.hasValue_algebraMap c)
    have h := ((P.hasValue_algebraMap c).mul (huP.inv (neg_ne_zero.mpr hc))).add P.hasValue_one
    have hval : c * (-c)⁻¹ + 1 = 0 := by
      rw [inv_neg, mul_neg, mul_inv_cancel₀ hc]
      exact neg_add_cancel 1
    rw [hval] at h
    exact h
  have hziQ : Q.HasValue z⁻¹ 0 := by
    rw [hzexpr, inv_div, div_eq_mul_inv]
    have huQ : Q.HasValue u 0 := by
      simpa only [sub_self] using hQ.sub (Q.hasValue_algebraMap c)
    simpa only [zero_mul] using huQ.mul (hQ.inv hc)
  have hzm : z - 1 ≠ 0 := by
    intro h
    have hz1 := sub_eq_zero.mp h
    rw [hz1, one_mul] at hzu
    apply ha
    dsimp [u] at hzu
    linear_combination -hzu
  have hrecover : a * z / (z - 1) = x := by
    apply (div_eq_iff hzm).mpr
    have hh : z * (x - a) = x := hzu
    linear_combination -hh
  have hmem : a * z / (z - 1) ∈ K⟮z⟯ :=
    (K⟮z⟯).div_mem
      ((K⟮z⟯).mul_mem ((K⟮z⟯).algebraMap_mem c) (IntermediateField.mem_adjoin_simple_self K z))
      ((K⟮z⟯).sub_mem (IntermediateField.mem_adjoin_simple_self K z) (K⟮z⟯).one_mem)
  rw [hrecover] at hmem
  exact ⟨z, hzmin, hzP, hziQ, hmem⟩

end AnabelianGeometry.FunctionField
