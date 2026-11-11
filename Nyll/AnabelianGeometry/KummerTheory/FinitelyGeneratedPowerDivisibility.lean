/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.KummerTheory.NumberFieldPowerDivisibility
public import Nyll.GaloisCohomology.FieldTheory.FinitelyGeneratedCharZero
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FinitelyGeneratedValuationDetection
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants

/-!
# Power divisibility in finitely generated characteristic-zero fields

Nonintegral elements are detected by actual discrete valuations. Algebraic
elements and roots of their powers lie in the finite field of constants.
-/

@[expose] public section

noncomputable section

namespace AnabelianGeometry.KummerTheory

universe u

variable {K : Type u} [Field K]

/-- A nonintegral element of a finitely generated field is detected by an
integer character of its actual multiplicative group. -/
theorem exists_integer_character_ne_one_of_not_integral
    (hfg : Field.FG K) (a : Kˣ) (ha : ¬ IsIntegral ℤ (a : K)) :
    ∃ f : Kˣ →* Multiplicative ℤ, f a ≠ 1 := by
  obtain ⟨W, hW, haW⟩ :=
    FieldTheory.exists_discreteValuationSubring_inv_nonunit_of_not_integral
      K hfg (a : K) ha
  have : IsDiscreteValuationRing W := hW
  let v : Valuation K (WithZero (Multiplicative ℤ)) :=
    (IsDiscreteValuationRing.maximalIdeal W).valuation K
  let e : W ≃+* v.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := W) (K := K)
  let y : W := ⟨(a : K)⁻¹, W.nonunits_le haW⟩
  have hy : ¬ IsUnit y :=
    (IsLocalRing.mem_maximalIdeal y).mp (W.coe_mem_nonunits_iff.mp haW)
  have hey : e y ∈ IsLocalRing.maximalIdeal v.valuationSubring := by
    apply (IsLocalRing.mem_maximalIdeal (e y)).mpr
    intro hu
    have hback := hu.map e.symm.toMonoidHom
    change IsUnit (e.symm (e y)) at hback
    rw [e.symm_apply_apply] at hback
    exact hy hback
  have hlt : v ((a : K)⁻¹) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := v)).mp hey
  have hva : v (a : K) ≠ 1 := by
    intro h
    rw [map_inv₀, h, inv_one] at hlt
    exact lt_irrefl _ hlt
  let f : Kˣ →* Multiplicative ℤ :=
    WithZero.unitsWithZeroEquiv.toMonoidHom.comp (Units.map v.toMonoidHom)
  refine ⟨f, ?_⟩
  intro h
  have hu : Units.map v.toMonoidHom a = 1 :=
    WithZero.unitsWithZeroEquiv.injective (h.trans (map_one _).symm)
  exact hva (congrArg Units.val hu)

variable [CharZero K]

/-- Nonconstant units admit a nonzero integer character, with no
finite-generation hypothesis on the entire multiplicative group. -/
theorem fg_exists_integer_character_ne_one_of_nonconstant
    (hfg : Field.FG K) (a : Kˣ)
    (ha : (a : K) ∉ algebraicClosure ℚ K) :
    ∃ f : Kˣ →* Multiplicative ℤ, f a ≠ 1 := by
  apply exists_integer_character_ne_one_of_not_integral hfg a
  intro hint
  exact ha (mem_algebraicClosure_iff'.mpr hint.tower_top)

/-- Uniform denominator bounds for powers over a finitely generated
characteristic-zero field. Roots remain in the original field. -/
theorem fg_exists_power_divisibility_bound
    (hfg : Field.FG K) (a : Kˣ) (ha : ¬ IsOfFinOrder a) :
    ∃ M : ℕ+, ∀ (e : ℤ) (n : ℕ+) (d : Kˣ),
      a ^ e = d ^ (n : ℕ) → (n : ℤ) ∣ e * (M : ℤ) := by
  have : Algebra.EssFiniteType ℚ K := FieldTheory.essFiniteType_rat_of_fg K hfg
  let C := algebraicClosure ℚ K
  have : Module.Finite ℚ C := FieldTheory.finite_algebraic_subextension ℚ C K
  have : NumberField C := {}
  by_cases haC : (a : K) ∈ C
  · let aC : Cˣ := Units.mk0 (⟨(a : K), haC⟩ : C) (by
      intro h
      exact a.ne_zero (congrArg (fun z : C => (z : K)) h))
    let inc : Cˣ →* Kˣ := Units.map C.val.toMonoidHom
    have hinc : inc aC = a := Units.ext rfl
    have haCinf : ¬ IsOfFinOrder aC := by
      intro h
      exact ha (hinc ▸ inc.isOfFinOrder h)
    obtain ⟨M, hM⟩ := exists_power_divisibility_bound aC haCinf
    refine ⟨M, ?_⟩
    intro e n d h
    have hdC : (d : K) ∈ C := by
      apply mem_algebraicClosure_iff'.mpr
      apply IsIntegral.of_pow n.pos
      have hval : (a : K) ^ e = (d : K) ^ (n : ℕ) := by
        simpa only [Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val]
          using congrArg Units.val h
      rw [← hval]
      exact mem_algebraicClosure_iff'.mp (C.toSubfield.zpow_mem haC e)
    let dC : Cˣ := Units.mk0 (⟨(d : K), hdC⟩ : C) (by
      intro hzero
      exact d.ne_zero (congrArg (fun z : C => (z : K)) hzero))
    apply hM e n dC
    apply Units.map_injective C.val.injective
    change inc (aC ^ e) = inc (dC ^ (n : ℕ))
    have hdinc : inc dC = d := Units.ext rfl
    rw [map_zpow, map_pow, hinc, hdinc]
    exact h
  · obtain ⟨f, hf⟩ := fg_exists_integer_character_ne_one_of_nonconstant hfg a haC
    let z : ℤ := Multiplicative.toAdd (f a)
    have hz : z ≠ 0 := by
      intro h
      exact hf (Multiplicative.toAdd.injective h)
    refine ⟨⟨z.natAbs, Int.natAbs_pos.mpr hz⟩, ?_⟩
    intro e n d h
    have hd : (n : ℤ) ∣ e * z := integer_character_dvd_of_zpow_eq_pow f a d e n h
    change (n : ℤ) ∣ e * (z.natAbs : ℤ)
    rcases le_total 0 z with hpos | hneg
    · simpa only [Int.natCast_natAbs, abs_of_nonneg hpos] using hd
    · have hd' := dvd_neg.mpr hd
      simpa only [Int.natCast_natAbs, abs_of_nonpos hneg, mul_neg] using hd'

/-- The multiplicative group of a finitely generated characteristic-zero
field has no nontrivial element divisible by every positive integer. -/
theorem fg_eq_one_of_forall_exists_pow
    (hfg : Field.FG K) (a : Kˣ)
    (h : ∀ n : ℕ+, ∃ d : Kˣ, d ^ (n : ℕ) = a) : a = 1 := by
  have : Algebra.EssFiniteType ℚ K := FieldTheory.essFiniteType_rat_of_fg K hfg
  let C := algebraicClosure ℚ K
  have : Module.Finite ℚ C := FieldTheory.finite_algebraic_subextension ℚ C K
  have : NumberField C := {}
  have haC : (a : K) ∈ C := by
    by_contra hnot
    obtain ⟨f, hf⟩ := fg_exists_integer_character_ne_one_of_nonconstant hfg a hnot
    have heq : f a = 1 := eq_one_of_forall_exists_pow (f a) (by
      intro n
      obtain ⟨d, hd⟩ := h n
      exact ⟨f d, by rw [← map_pow, hd]⟩)
    exact hf heq
  let aC : Cˣ := Units.mk0 (⟨(a : K), haC⟩ : C) (by
    intro hzero
    exact a.ne_zero (congrArg (fun z : C => (z : K)) hzero))
  have hroots : ∀ n : ℕ+, ∃ d : Cˣ, d ^ (n : ℕ) = aC := by
    intro n
    obtain ⟨d, hd⟩ := h n
    have hdC : (d : K) ∈ C := by
      apply mem_algebraicClosure_iff'.mpr
      apply IsIntegral.of_pow n.pos
      have hval : (d : K) ^ (n : ℕ) = (a : K) := congrArg Units.val hd
      rw [hval]
      exact mem_algebraicClosure_iff'.mp haC
    refine ⟨Units.mk0 (⟨(d : K), hdC⟩ : C) (by
      intro hzero
      exact d.ne_zero (congrArg (fun z : C => (z : K)) hzero)), ?_⟩
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val hd
  have hmem : aC ∈ Subgroup.zpowers (1 : Cˣ) := by
    apply numberField_mem_zpowers_of_forall_mem_sup_powers aC 1
    intro n
    obtain ⟨d, hd⟩ := hroots n
    exact (le_sup_right : (powMonoidHom (α := Cˣ) (n : ℕ)).range ≤
      Subgroup.zpowers 1 ⊔ (powMonoidHom (α := Cˣ) (n : ℕ)).range) ⟨d, hd⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have heq : aC = 1 := by simpa only [one_zpow] using hj.symm
  exact Units.ext (congrArg (fun z : Cˣ => ((z : C) : K)) heq)

end AnabelianGeometry.KummerTheory
