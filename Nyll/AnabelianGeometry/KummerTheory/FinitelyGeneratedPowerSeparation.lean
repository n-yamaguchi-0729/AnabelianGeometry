/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.KummerTheory.FinitelyGeneratedPowerDivisibility
public import Nyll.AnabelianGeometry.KummerTheory.CoprimeCoefficientCyclicClasses
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants
public import Nyll.GaloisCohomology.FieldTheory.FinitelyGeneratedCharZero

/-!
# Cyclic power separation over finitely generated fields

An integer character detecting the cyclic generator reduces separation to
the absence of infinitely divisible elements. If every integer character
vanishes, discrete valuations force both elements into the number field
of algebraic constants, where the actual power witnesses also descend.
-/

@[expose] public section

noncomputable section

namespace AnabelianGeometry.KummerTheory

private theorem character_mem_zpowers_of_forall_mem_sup_powers
    {G : Type*} [CommGroup G] (f : G →* Multiplicative ℤ) (a b : G)
    (h : ∀ n : ℕ+, a ∈ Subgroup.zpowers b ⊔
      (powMonoidHom (α := G) (n : ℕ)).range) :
    f a ∈ Subgroup.zpowers (f b) := by
  apply mem_of_forall_mem_sup_powers
  intro n
  obtain ⟨c, hc, y, hy, hcy⟩ := Subgroup.mem_sup.mp (h n)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  obtain ⟨d, hd⟩ := hy
  change d ^ (n : ℕ) = y at hd
  apply Subgroup.mem_sup.mpr
  refine ⟨(f b) ^ j, (Subgroup.zpowers (f b)).zpow_mem
    (Subgroup.mem_zpowers (f b)) j,
    (f d) ^ (n : ℕ), ⟨f d, rfl⟩, ?_⟩
  rw [← map_zpow, ← map_pow, ← map_mul, hd, hcy]

/-- A cyclic subgroup whose generator has a nonzero integer character is
closed under all-power tests, provided the ambient group has no nontrivial
element divisible by every positive integer. -/
theorem mem_zpowers_of_integer_character_of_forall_mem_sup_powers
    {G : Type*} [CommGroup G]
    (hsep : ∀ x : G, (∀ n : ℕ+, ∃ y : G, y ^ (n : ℕ) = x) → x = 1)
    (a b : G) (f : G →* Multiplicative ℤ) (hfb : f b ≠ 1)
    (h : ∀ n : ℕ+, a ∈ Subgroup.zpowers b ⊔
      (powMonoidHom (α := G) (n : ℕ)).range) :
    a ∈ Subgroup.zpowers b := by
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp
    (character_mem_zpowers_of_forall_mem_sup_powers f a b h)
  let x := a / b ^ e
  have hfx : f x = 1 := by
    change f (a / b ^ e) = 1
    rw [map_div, map_zpow, he, div_self']
  have hx (n : ℕ+) : x ∈ Subgroup.zpowers b ⊔
      (powMonoidHom (α := G) (n : ℕ)).range := by
    exact (Subgroup.zpowers b ⊔ (powMonoidHom (α := G) (n : ℕ)).range).div_mem
      (h n) ((le_sup_left : Subgroup.zpowers b ≤ Subgroup.zpowers b ⊔
        (powMonoidHom (α := G) (n : ℕ)).range)
        ((Subgroup.zpowers b).zpow_mem (Subgroup.mem_zpowers b) e))
  let B : ℤ := Multiplicative.toAdd (f b)
  have hB : B ≠ 0 := by
    intro hzero
    exact hfb (Multiplicative.toAdd.injective hzero)
  have hxone : x = 1 := hsep x (by
    intro n
    let N : ℕ+ := ⟨(n : ℕ) * B.natAbs, Nat.mul_pos n.pos (Int.natAbs_pos.mpr hB)⟩
    obtain ⟨c, hc, y, hy, hcy⟩ := Subgroup.mem_sup.mp (hx N)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    obtain ⟨d, hd⟩ := hy
    change d ^ (N : ℕ) = y at hd
    rw [← hd] at hcy
    let D : ℤ := Multiplicative.toAdd (f d)
    have hrel : j * B + (n : ℤ) * |B| * D = 0 := by
      have ht := congrArg (fun z : G => Multiplicative.toAdd (f z)) hcy
      rw [map_mul, map_zpow, map_pow, hfx] at ht
      change j • B + ((n : ℕ) * B.natAbs) • D = 0 at ht
      simpa only [zsmul_eq_mul, nsmul_eq_mul, Int.cast_id, Nat.cast_mul,
        Int.natCast_natAbs] using ht
    have hj : (n : ℤ) ∣ j := by
      rcases le_total 0 B with hpos | hneg
      · refine ⟨-D, ?_⟩
        apply mul_left_cancel₀ hB
        rw [abs_of_nonneg hpos] at hrel
        calc
          B * j = -((n : ℤ) * B * D) := by nlinarith [hrel]
          _ = B * ((n : ℤ) * -D) := by ring
      · refine ⟨D, ?_⟩
        apply mul_left_cancel₀ hB
        rw [abs_of_nonpos hneg] at hrel
        calc
          B * j = (n : ℤ) * B * D := by nlinarith [hrel]
          _ = B * ((n : ℤ) * D) := by ring
    obtain ⟨k, hk⟩ := hj
    refine ⟨b ^ k * d ^ B.natAbs, ?_⟩
    have hbpow : (b ^ k) ^ (n : ℕ) = b ^ j := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm k (n : ℤ), ← hk]
    have hdpow : (d ^ B.natAbs) ^ (n : ℕ) = d ^ (N : ℕ) := by
      rw [← pow_mul, Nat.mul_comm]
      rfl
    rw [mul_pow, hbpow, hdpow]
    exact hcy)
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨e, ?_⟩
  exact (div_eq_one.mp hxone).symm

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- All positive power quotients of a finitely generated field determine
membership in an actual cyclic subgroup of its multiplicative group. -/
theorem fg_mem_zpowers_of_forall_mem_sup_powers
    (hfg : Field.FG K) (a b : Kˣ)
    (h : ∀ n : ℕ+, a ∈ Subgroup.zpowers b ⊔
      (powMonoidHom (α := Kˣ) (n : ℕ)).range) :
    a ∈ Subgroup.zpowers b := by
  classical
  by_cases hb : ∃ f : Kˣ →* Multiplicative ℤ, f b ≠ 1
  · obtain ⟨f, hf⟩ := hb
    exact mem_zpowers_of_integer_character_of_forall_mem_sup_powers
      (fg_eq_one_of_forall_exists_pow hfg) a b f hf h
  have hbchar (f : Kˣ →* Multiplicative ℤ) : f b = 1 :=
    not_ne_iff.mp (fun hf => hb ⟨f, hf⟩)
  have hachar (f : Kˣ →* Multiplicative ℤ) : f a = 1 := by
    obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp
      (character_mem_zpowers_of_forall_mem_sup_powers f a b h)
    simpa only [hbchar f, one_zpow] using he.symm
  let C := algebraicClosure ℚ K
  have : Algebra.EssFiniteType ℚ K := FieldTheory.essFiniteType_rat_of_fg K hfg
  have : Module.Finite ℚ C := FieldTheory.finite_algebraic_subextension ℚ C K
  have : NumberField C := {}
  have hconstant (z : Kˣ) (hz : ∀ f : Kˣ →* Multiplicative ℤ, f z = 1) :
      (z : K) ∈ C := by
    by_contra hnot
    obtain ⟨f, hf⟩ := fg_exists_integer_character_ne_one_of_nonconstant hfg z hnot
    exact hf (hz f)
  have haC : (a : K) ∈ C := hconstant a hachar
  have hbC : (b : K) ∈ C := hconstant b hbchar
  let aC : Cˣ := Units.mk0 (⟨(a : K), haC⟩ : C) (by
    intro hzero
    exact a.ne_zero (congrArg (fun z : C => (z : K)) hzero))
  let bC : Cˣ := Units.mk0 (⟨(b : K), hbC⟩ : C) (by
    intro hzero
    exact b.ne_zero (congrArg (fun z : C => (z : K)) hzero))
  let inc : Cˣ →* Kˣ := Units.map C.val.toMonoidHom
  have hinc : Function.Injective inc := Units.map_injective C.val.injective
  have hinca : inc aC = a := Units.ext rfl
  have hincb : inc bC = b := Units.ext rfl
  have hmem : aC ∈ Subgroup.zpowers bC := by
    apply numberField_mem_zpowers_of_forall_mem_sup_powers aC bC
    intro n
    obtain ⟨c, hc, y, hy, hcy⟩ := Subgroup.mem_sup.mp (h n)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    obtain ⟨d, hd⟩ := hy
    change d ^ (n : ℕ) = y at hd
    rw [← hd] at hcy
    have hdC : (d : K) ∈ C := by
      apply mem_algebraicClosure_iff'.mpr
      apply IsIntegral.of_pow n.pos
      have hval : (b : K) ^ j * (d : K) ^ (n : ℕ) = (a : K) := by
        simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val,
          Units.val_pow_eq_pow_val] using congrArg Units.val hcy
      have heq : (d : K) ^ (n : ℕ) = (a : K) / (b : K) ^ j := by
        apply (eq_div_iff (zpow_ne_zero j b.ne_zero)).mpr
        rw [mul_comm]
        exact hval
      rw [heq]
      exact mem_algebraicClosure_iff'.mp (C.div_mem haC (C.toSubfield.zpow_mem hbC j))
    let dC : Cˣ := Units.mk0 (⟨(d : K), hdC⟩ : C) (by
      intro hzero
      exact d.ne_zero (congrArg (fun z : C => (z : K)) hzero))
    apply Subgroup.mem_sup.mpr
    refine ⟨bC ^ j, (Subgroup.zpowers bC).zpow_mem (Subgroup.mem_zpowers bC) j,
      dC ^ (n : ℕ), ⟨dC, rfl⟩, ?_⟩
    have hincd : inc dC = d := Units.ext rfl
    apply hinc
    rw [map_mul, map_zpow, map_pow, hinca, hincb, hincd]
    exact hcy
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp hmem
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨e, ?_⟩
  have he' := congrArg inc he
  rw [map_zpow, hincb, hinca] at he'
  exact he'

/-- Equality of all power-quotient cyclic subgroups recovers the original
cyclic subgroups over a finitely generated characteristic-zero field. -/
theorem fg_zpowers_eq_of_forall_sup_powers_eq
    (hfg : Field.FG K) (a b : Kˣ)
    (h : ∀ n : ℕ+,
      Subgroup.zpowers a ⊔ (powMonoidHom (α := Kˣ) (n : ℕ)).range =
      Subgroup.zpowers b ⊔ (powMonoidHom (α := Kˣ) (n : ℕ)).range) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  apply le_antisymm
  · apply Subgroup.zpowers_le.mpr
    apply fg_mem_zpowers_of_forall_mem_sup_powers hfg a b
    intro n
    rw [← h n]
    exact (le_sup_left : Subgroup.zpowers a ≤ Subgroup.zpowers a ⊔
      (powMonoidHom (α := Kˣ) (n : ℕ)).range) (Subgroup.mem_zpowers a)
  · apply Subgroup.zpowers_le.mpr
    apply fg_mem_zpowers_of_forall_mem_sup_powers hfg b a
    intro n
    rw [h n]
    exact (le_sup_left : Subgroup.zpowers b ≤ Subgroup.zpowers b ⊔
      (powMonoidHom (α := Kˣ) (n : ℕ)).range) (Subgroup.mem_zpowers b)

/-- Invertible coefficient exponents at every positive modulus determine
the exact cyclic subgroup over a finitely generated characteristic-zero field. -/
theorem fg_zpowers_eq_of_forall_unit_power_classes
    (hfg : Field.FG K) (a b : Kˣ)
    (h : ∀ n : ℕ+, ∃ u v : (ZMod (n : ℕ))ˣ, ∃ d : Kˣ,
      b ^ (u : ZMod (n : ℕ)).val =
        a ^ (v : ZMod (n : ℕ)).val * d ^ (n : ℕ)) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  apply fg_zpowers_eq_of_forall_sup_powers_eq hfg a b
  intro n
  obtain ⟨u, v, d, hd⟩ := h n
  exact zpowers_sup_power_range_eq_of_coprime_power_relation a b d (n : ℕ)
    (u : ZMod (n : ℕ)).val (v : ZMod (n : ℕ)).val
    (ZMod.val_coe_unit_coprime u) (ZMod.val_coe_unit_coprime v) hd

end AnabelianGeometry.KummerTheory
