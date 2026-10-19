/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Cyclic radical descent from the exact arithmetic norm kernel -/

noncomputable section

open scoped BigOperators

namespace AnabelianGeometry.KummerTheory

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The actual conjugate ratio is a power of the specified primitive root. -/
theorem exists_root_ratio_exponent
    {N : ℕ} [NeZero N] {ζ z : E} (hζ : IsPrimitiveRoot ζ N)
    (σ : Gal(E/F)) (hz : z ≠ 0)
    (hzN : z ^ N ∈ Set.range (algebraMap F E)) :
    ∃ t : ℕ, t < N ∧ σ z / z = ζ ^ t := by
  have hfix : σ (z ^ N) = z ^ N := by
    obtain ⟨a, ha⟩ := hzN
    rw [← ha, σ.commutes]
  have hratio : (σ z / z) ^ N = 1 := by
    rw [div_pow, ← map_pow, hfix, div_self (pow_ne_zero _ hz)]
  obtain ⟨t, ht, hpow⟩ := hζ.eq_pow_of_pow_eq_one hratio
  exact ⟨t, ht, hpow.symm⟩

/-- Iteration gives the geometric-sum exponent without assuming a norm relation. -/
theorem radical_iterate
    (σ : Gal(E/F)) (ζ z : E) (u t : ℕ)
    (hζσ : σ ζ = ζ ^ u) (hzσ : σ z = ζ ^ t * z) (k : ℕ) :
    (σ ^ k) z = ζ ^ (t * ∑ j ∈ Finset.range k, u ^ j) * z := by
  induction k with
  | zero =>
      simp only [pow_zero, AlgEquiv.one_apply, Finset.range_zero,
        Finset.sum_empty, mul_zero, one_mul]
  | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow,
        hζσ, hzσ, ← pow_mul, ← mul_assoc, ← pow_add]
      congr 2
      rw [geom_sum_succ]
      ring

/-- The actual automorphism's period implies the root-ratio norm relation. -/
theorem root_ratio_norm_relation
    {N : ℕ} [NeZero N] {ζ z : E} (hζ : IsPrimitiveRoot ζ N)
    (σ : Gal(E/F)) (u : (ZMod N)ˣ)
    (hζσ : σ ζ = ζ ^ (u : ZMod N).val)
    (hz : z ≠ 0) (t : ℕ) (hzσ : σ z = ζ ^ t * z)
    (d : ℕ) (hσd : σ ^ d = 1) :
    (∑ j ∈ Finset.range d, (u : ZMod N) ^ j) * (t : ZMod N) = 0 := by
  have hiter := radical_iterate σ ζ z (u : ZMod N).val t hζσ hzσ d
  rw [hσd, AlgEquiv.one_apply] at hiter
  have hpow : ζ ^ (t * ∑ j ∈ Finset.range d, (u : ZMod N).val ^ j) = 1 := by
    exact mul_right_cancel₀ hz (hiter.symm.trans (one_mul z).symm)
  have hdiv : N ∣ t * ∑ j ∈ Finset.range d, (u : ZMod N).val ^ j :=
    (hζ.pow_eq_one_iff_dvd _).mp hpow
  have hcast : ((t * ∑ j ∈ Finset.range d, (u : ZMod N).val ^ j : ℕ) : ZMod N) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_pow,
    ZMod.natCast_zmod_val, mul_comm] using hcast

/-- A solution of the exponent equation gives an actual fixed radical. -/
theorem corrected_radical_fixed
    {N : ℕ} [NeZero N] {ζ z : E} (hζ : IsPrimitiveRoot ζ N)
    (σ : Gal(E/F)) (u : (ZMod N)ˣ)
    (hζσ : σ ζ = ζ ^ (u : ZMod N).val)
    (t : ℕ) (hzσ : σ z = ζ ^ t * z) (y : ZMod N)
    (hy : ((u : ZMod N) - 1) * y = (t : ZMod N)) :
    σ (z / ζ ^ y.val) = z / ζ ^ y.val := by
  have hy' : (u : ZMod N) * y = (t : ZMod N) + y := by
    rw [sub_mul, one_mul] at hy
    exact sub_eq_iff_eq_add.mp hy
  have hmod : (u : ZMod N).val * y.val ≡ t + y.val [MOD N] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_mul, Nat.cast_add, ZMod.natCast_zmod_val] using hy'
  have hp : ζ ^ ((u : ZMod N).val * y.val) = ζ ^ (t + y.val) :=
    pow_eq_pow_of_modEq hmod hζ.pow_eq_one
  have hden : σ (ζ ^ y.val) = ζ ^ t * ζ ^ y.val := by
    rw [map_pow, hζσ, ← pow_mul, hp, pow_add]
  have hζ0 : ζ ≠ 0 := (hζ.isUnit (NeZero.ne N)).ne_zero
  calc
    σ (z / ζ ^ y.val) = σ z / σ (ζ ^ y.val) := map_div₀ σ z (ζ ^ y.val)
    _ = (ζ ^ t * z) / (ζ ^ t * ζ ^ y.val) := by rw [hzσ, hden]
    _ = z / ζ ^ y.val := by field_simp [hζ0]

/-- Fixedness under a generator implies fixedness under the full finite group. -/
theorem fixed_by_all_of_fixed_by_generator
    [FiniteDimensional F E] (σ : Gal(E/F))
    (hgen : ∀ τ : Gal(E/F), τ ∈ Subgroup.zpowers σ)
    (x : E) (hx : σ x = x) : ∀ τ : Gal(E/F), τ x = x := by
  have hpow : ∀ k : ℕ, (σ ^ k) x = x := by
    intro k
    induction k with
    | zero => rw [pow_zero, AlgEquiv.one_apply]
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hx]
  intro τ
  have hmem : τ ∈ Submonoid.powers σ := mem_powers_iff_mem_zpowers.mpr (hgen τ)
  obtain ⟨k, hk⟩ := hmem
  rw [← hk]
  exact hpow k

/-- Conditional descent with the arithmetic norm-kernel equality explicit. -/
theorem cyclic_radical_descent_of_norm_kernel
    [FiniteDimensional F E] [IsGalois F E]
    {N : ℕ} [NeZero N] {ζ : E} (hζ : IsPrimitiveRoot ζ N)
    (σ : Gal(E/F)) (hgen : ∀ τ : Gal(E/F), τ ∈ Subgroup.zpowers σ)
    (u : (ZMod N)ˣ) (hζσ : σ ζ = ζ ^ (u : ZMod N).val)
    (hkernel : ∀ t : ZMod N,
      (∑ j ∈ Finset.range (orderOf σ), (u : ZMod N) ^ j) * t = 0 ↔
        ∃ y : ZMod N, ((u : ZMod N) - 1) * y = t)
    (z : E) (hzN : z ^ N ∈ Set.range (algebraMap F E)) :
    ∃ y : ZMod N, ∃ a : F, algebraMap F E a = z / ζ ^ y.val := by
  by_cases hz : z = 0
  · refine ⟨0, 0, ?_⟩
    simp [hz]
  obtain ⟨t, _, ht⟩ := exists_root_ratio_exponent hζ σ hz hzN
  have hzσ : σ z = ζ ^ t * z := (div_eq_iff hz).mp ht
  have hnorm :
      (∑ j ∈ Finset.range (orderOf σ), (u : ZMod N) ^ j) * (t : ZMod N) = 0 :=
    root_ratio_norm_relation hζ σ u hζσ hz t hzσ (orderOf σ) (pow_orderOf_eq_one σ)
  obtain ⟨y, hy⟩ := (hkernel (t : ZMod N)).mp hnorm
  have hfixed : σ (z / ζ ^ y.val) = z / ζ ^ y.val :=
    corrected_radical_fixed hζ σ u hζσ t hzσ y hy
  have hall : ∀ τ : Gal(E/F), τ (z / ζ ^ y.val) = z / ζ ^ y.val :=
    fixed_by_all_of_fixed_by_generator σ hgen (z / ζ ^ y.val) hfixed
  have hbase : z / ζ ^ y.val ∈ Set.range (algebraMap F E) :=
    (IsGalois.mem_range_algebraMap_iff_fixed (F := F) (E := E) (z / ζ ^ y.val)).mpr hall
  obtain ⟨a, ha⟩ := hbase
  exact ⟨y, a, ha⟩

end AnabelianGeometry.KummerTheory
