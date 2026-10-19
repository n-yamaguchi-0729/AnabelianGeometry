/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.CyclicRadicalDescent
import Nyll.AnabelianGeometry.KummerTheory.GoodPrimePowerNormKernel
import Nyll.AnabelianGeometry.KummerTheory.TwoPowerCyclotomicCyclicity
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.Tactic

/-! # Exact prime-power radical descent in the actual cyclotomic extension -/

noncomputable section

open scoped BigOperators

namespace AnabelianGeometry.KummerTheory

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The specified primitive root generates the actual cyclotomic extension. -/
theorem isCyclotomicExtension_of_primitive_adjoin
    {N : ℕ} [NeZero N] {ζ : E} (hζ : IsPrimitiveRoot ζ N)
    (hgen : Algebra.adjoin F ({ζ} : Set E) = ⊤) :
    IsCyclotomicExtension {N} F E := by
  apply (IsCyclotomicExtension.iff_singleton N F E).mpr
  refine ⟨⟨ζ, hζ⟩, ?_⟩
  have hle : Algebra.adjoin F ({ζ} : Set E) ≤
      Algebra.adjoin F {x : E | x ^ N = 1} := by
    apply Algebra.adjoin_mono
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact hζ.pow_eq_one
  rw [hgen] at hle
  intro x
  exact hle (show x ∈ (⊤ : Subalgebra F E) from trivial)

/-- Faithfulness of the character follows from actual cyclotomic generation. -/
theorem autToPow_injective_of_adjoin
    {N : ℕ} [NeZero N] {ζ : E} (hζ : IsPrimitiveRoot ζ N)
    (hgen : Algebra.adjoin F ({ζ} : Set E) = ⊤) :
    Function.Injective (hζ.autToPow F) := by
  let : IsCyclotomicExtension {N} F E :=
    isCyclotomicExtension_of_primitive_adjoin hζ hgen
  exact hζ.autToPow_injective F

/-- A primitive fourth root in the base fixes all actual fourth roots. -/
theorem fourth_roots_fixed_of_base_primitive
    {η : F} (hη : IsPrimitiveRoot η 4)
    (σ : Gal(E/F)) (x : E) (hx : x ^ 4 = 1) : σ x = x := by
  have hηE : IsPrimitiveRoot (algebraMap F E η) 4 :=
    hη.map_of_injective (algebraMap F E).injective
  obtain ⟨j, _, hj⟩ := hηE.eq_pow_of_pow_eq_one hx
  rw [← hj, map_pow, σ.commutes]

/-- Fixing fourth roots forces the actual character to be one modulo four. -/
theorem twoPower_autToPow_mod_four
    (s : ℕ) [NeZero (2 ^ (s + 2))]
    {ζ : E} (hζ : IsPrimitiveRoot ζ (2 ^ (s + 2)))
    (hfour : ∀ (τ : Gal(E/F)) (x : E), x ^ 4 = 1 → τ x = x)
    (σ : Gal(E/F)) :
    (((hζ.autToPow F σ : ZMod (2 ^ (s + 2))).val : ℕ) : ZMod 4) = 1 := by
  let ξ : E := ζ ^ (2 ^ s)
  have hξ : IsPrimitiveRoot ξ 4 := by
    apply IsPrimitiveRoot.pow (pow_pos (by decide : 0 < (2 : ℕ)) (s + 2)) hζ
    simp [pow_add]
  let v : ℕ := (hζ.autToPow F σ : ZMod (2 ^ (s + 2))).val
  have hfix : ξ ^ v = ξ := by
    calc
      ξ ^ v = (ζ ^ v) ^ (2 ^ s) := by
        dsimp only [ξ]
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = (σ ζ) ^ (2 ^ s) := by
        rw [show ζ ^ v = σ ζ from hζ.autToPow_spec F σ]
      _ = σ ξ := (map_pow σ ζ (2 ^ s)).symm
      _ = ξ := hfour σ ξ hξ.pow_eq_one
  have hred : ξ ^ (v % 4) = ξ ^ v :=
    pow_eq_pow_of_modEq (Nat.mod_modEq v 4) hξ.pow_eq_one
  have hrem : v % 4 = 1 := by
    apply hξ.pow_inj (Nat.mod_lt _ (by decide)) (by decide)
    exact hred.trans (hfix.trans (pow_one ξ).symm)
  change (v : ZMod 4) = 1
  apply (ZMod.natCast_eq_natCast_iff v 1 4).mpr
  change v % 4 = 1 % 4
  simpa using hrem

/-- The representative congruence is an exact divisibility statement. -/
theorem int_four_dvd_sub_one_of_zmod_four (v : ℕ) (hv : (v : ZMod 4) = 1) :
    (4 : ℤ) ∣ ((v : ℤ) - 1) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_one, hv, sub_self]

/-- Cyclicity and the good-unit condition for the actual cyclotomic character. -/
theorem goodPrimePower_cyclotomic_character
    {p r : ℕ} [NeZero (p ^ r)] (hp : p.Prime) (hr : 0 < r)
    {ζ : E} (hζ : IsPrimitiveRoot ζ (p ^ r))
    (hgen : Algebra.adjoin F ({ζ} : Set E) = ⊤)
    (hfour : p = 2 → 2 ≤ r → ∃ η : F, IsPrimitiveRoot η 4) :
    IsCyclic Gal(E/F) ∧ ∀ σ : Gal(E/F), p = 2 →
      (4 : ℤ) ∣ (((hζ.autToPow F σ : ZMod (p ^ r)).val : ℤ) - 1) := by
  have hinj := autToPow_injective_of_adjoin hζ hgen
  by_cases hp2 : p = 2
  · subst p
    cases r with
    | zero => omega
    | succ r =>
        cases r with
        | zero =>
            let : IsCyclic (ZMod (2 ^ 1))ˣ := by
              change IsCyclic (ZMod 2)ˣ
              exact ZMod.isCyclic_units_two
            refine ⟨isCyclic_of_injective (hζ.autToPow F) hinj, ?_⟩
            intro σ _
            let u : (ZMod 2)ˣ := hζ.autToPow F σ
            have hv0 : (u : ZMod 2).val ≠ 0 := by
              intro hv
              apply u.ne_zero
              simpa [hv] using (ZMod.natCast_zmod_val (u : ZMod 2)).symm
            have hvlt : (u : ZMod 2).val < 2 := ZMod.val_lt (u : ZMod 2)
            have hv : (u : ZMod 2).val = 1 := by omega
            change (4 : ℤ) ∣ (((u : ZMod 2).val : ℤ) - 1)
            simp [hv]
        | succ s =>
            obtain ⟨η, hη⟩ := hfour rfl (by omega)
            have hfixed : ∀ (τ : Gal(E/F)) (x : E), x ^ 4 = 1 → τ x = x :=
              fun τ x hx => fourth_roots_fixed_of_base_primitive hη τ x hx
            have hmod (σ : Gal(E/F)) :
                (((hζ.autToPow F σ : ZMod (2 ^ (s + 2))).val : ℕ) : ZMod 4) = 1 :=
              twoPower_autToPow_mod_four s hζ hfixed σ
            have h4 : 4 ∣ 2 ^ (s + 2) := by
              refine ⟨2 ^ s, ?_⟩
              simp [pow_add, Nat.mul_comm]
            have hmap (σ : Gal(E/F)) : ZMod.unitsMap h4 (hζ.autToPow F σ) = 1 := by
              apply Units.ext
              change (ZMod.castHom h4 (ZMod 4))
                (hζ.autToPow F σ : ZMod (2 ^ (s + 2))) = 1
              rw [ZMod.castHom_apply, ZMod.cast_eq_val]
              exact hmod σ
            refine ⟨isCyclic_of_injective_twoPower_character
              s h4 (hζ.autToPow F) hinj hmap, ?_⟩
            intro σ _
            exact int_four_dvd_sub_one_of_zmod_four _ (hmod σ)
  · let : IsCyclic (ZMod (p ^ r))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 r
    refine ⟨isCyclic_of_injective (hζ.autToPow F) hinj, ?_⟩
    intro σ h
    exact (hp2 h).elim

/-- Exact prime-power descent, with no norm-kernel or cyclicity assumption. -/
theorem primePower_pow_descends_of_primitive_adjoin
    {p r : ℕ} (hp : p.Prime)
    {ζ : E} (hζ : IsPrimitiveRoot ζ (p ^ r))
    (hgen : Algebra.adjoin F ({ζ} : Set E) = ⊤)
    (hfour : p = 2 → 2 ≤ r → ∃ η : F, IsPrimitiveRoot η 4)
    (z : E) (hz : z ^ (p ^ r) ∈ Set.range (algebraMap F E)) :
    ∃ a : F, algebraMap F E (a ^ (p ^ r)) = z ^ (p ^ r) := by
  by_cases hr0 : r = 0
  · subst r
    obtain ⟨a, ha⟩ := hz
    exact ⟨a, by simpa only [pow_zero, pow_one] using ha⟩
  have hr : 0 < r := Nat.pos_of_ne_zero hr0
  let : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let : IsCyclotomicExtension {p ^ r} F E :=
    isCyclotomicExtension_of_primitive_adjoin hζ hgen
  let : FiniteDimensional F E := IsCyclotomicExtension.finiteDimensional {p ^ r} F E
  let : IsGalois F E := IsCyclotomicExtension.isGalois {p ^ r} F E
  obtain ⟨hcyclic, hgood⟩ := goodPrimePower_cyclotomic_character hp hr hζ hgen hfour
  let : IsCyclic Gal(E/F) := hcyclic
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(E/F))
  let χ : Gal(E/F) →* (ZMod (p ^ r))ˣ := hζ.autToPow F
  have hχ : Function.Injective χ := autToPow_injective_of_adjoin hζ hgen
  have horder : orderOf (χ σ) = orderOf σ := orderOf_injective χ hχ σ
  have hkernel (t : ZMod (p ^ r)) :
      (∑ j ∈ Finset.range (orderOf σ), (χ σ : ZMod (p ^ r)) ^ j) * t = 0 ↔
        ∃ y : ZMod (p ^ r), ((χ σ : ZMod (p ^ r)) - 1) * y = t := by
    simpa only [horder] using
      geomSum_orderOf_goodPrimePowerUnit_mul_eq_zero_iff hp (χ σ) (hgood σ) t
  have hζσ : σ ζ = ζ ^ (χ σ : ZMod (p ^ r)).val := (hζ.autToPow_spec F σ).symm
  obtain ⟨y, a, ha⟩ :=
    cyclic_radical_descent_of_norm_kernel hζ σ hσ (χ σ) hζσ hkernel z hz
  have hden : (ζ ^ y.val) ^ (p ^ r) = 1 := by
    rw [← pow_mul, Nat.mul_comm y.val (p ^ r), pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨a, ?_⟩
  rw [map_pow, ha, div_pow, hden, div_one]

/-- A base element acquiring a prime-power root already has that root in the base. -/
theorem exists_primePower_root_in_base
    {p r : ℕ} (hp : p.Prime) {ζ : E} (hζ : IsPrimitiveRoot ζ (p ^ r))
    (hgen : Algebra.adjoin F ({ζ} : Set E) = ⊤)
    (hfour : p = 2 → 2 ≤ r → ∃ η : F, IsPrimitiveRoot η 4)
    (b : F) (z : E) (hz : z ^ (p ^ r) = algebraMap F E b) :
    ∃ a : F, a ^ (p ^ r) = b := by
  obtain ⟨a, ha⟩ :=
    primePower_pow_descends_of_primitive_adjoin hp hζ hgen hfour z ⟨b, hz.symm⟩
  exact ⟨a, (algebraMap F E).injective (ha.trans hz)⟩

end AnabelianGeometry.KummerTheory
