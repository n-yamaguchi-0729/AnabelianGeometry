/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.KummerTheory.NumberFieldPrimePowerSeparation
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic

/-!
# Exact cyclic recovery from invertible power-class exponents

An equality of two power classes with exponents prime to the modulus gives
identical cyclic enlargements by all modulus powers. Over a number field,
prime-power separation then recovers the exact cyclic subgroups, including
their torsion. No radical field equality or cyclotomic descent is assumed.
-/

namespace AnabelianGeometry.KummerTheory

/-- A relation with both coefficient exponents prime to `n` identifies the
cyclic subgroups after adjoining all `n`th powers. -/
theorem zpowers_sup_power_range_eq_of_coprime_power_relation
    {G : Type*} [CommGroup G] (a b d : G) (n u v : ℕ)
    (hu : u.Coprime n) (hv : v.Coprime n)
    (h : b ^ u = a ^ v * d ^ n) :
    Subgroup.zpowers a ⊔ (powMonoidHom (α := G) n).range =
      Subgroup.zpowers b ⊔ (powMonoidHom (α := G) n).range := by
  let P : Subgroup G := (powMonoidHom (α := G) n).range
  have hroot (H : Subgroup G) (hP : P ≤ H) (x : G) (m : ℕ)
      (hmn : m.Coprime n) (hm : x ^ m ∈ H) : x ∈ H := by
    have hqm : ((QuotientGroup.mk' H) x) ^ m = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff (x ^ m)).mpr hm
    have hqn : ((QuotientGroup.mk' H) x) ^ n = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff (x ^ n)).mpr (hP ⟨x, rfl⟩)
    exact (QuotientGroup.eq_one_iff x).mp
      ((pow_eq_one_iff_of_coprime hmn).mp ⟨hqm, hqn⟩)
  have hbPow : b ^ u ∈ Subgroup.zpowers a ⊔ P := by
    rw [h]
    apply Subgroup.mul_mem
    · exact (le_sup_left : Subgroup.zpowers a ≤ Subgroup.zpowers a ⊔ P)
        ((Subgroup.zpowers a).pow_mem (Subgroup.mem_zpowers a) v)
    · exact (le_sup_right : P ≤ Subgroup.zpowers a ⊔ P)
        (show d ^ n ∈ P from ⟨d, rfl⟩)
  have haPow : a ^ v ∈ Subgroup.zpowers b ⊔ P := by
    have hb : b ^ u ∈ Subgroup.zpowers b ⊔ P :=
      (le_sup_left : Subgroup.zpowers b ≤ Subgroup.zpowers b ⊔ P)
        ((Subgroup.zpowers b).pow_mem (Subgroup.mem_zpowers b) u)
    have hd : d ^ n ∈ Subgroup.zpowers b ⊔ P :=
      (le_sup_right : P ≤ Subgroup.zpowers b ⊔ P)
        (show d ^ n ∈ P from ⟨d, rfl⟩)
    have hmul := (Subgroup.zpowers b ⊔ P).mul_mem hb
      ((Subgroup.zpowers b ⊔ P).inv_mem hd)
    rwa [h, mul_inv_cancel_right] at hmul
  have ha : a ∈ Subgroup.zpowers b ⊔ P :=
    hroot (Subgroup.zpowers b ⊔ P) le_sup_right a v hv haPow
  have hb : b ∈ Subgroup.zpowers a ⊔ P :=
    hroot (Subgroup.zpowers a ⊔ P) le_sup_right b u hu hbPow
  exact le_antisymm
    (sup_le (Subgroup.zpowers_le.mpr ha) le_sup_right)
    (sup_le (Subgroup.zpowers_le.mpr hb) le_sup_right)

/-- Over the original number field, equality of power classes up to two
invertible coefficient exponents at every positive modulus recovers the
exact cyclic subgroup. The coefficient units may depend on the modulus. -/
theorem numberField_zpowers_eq_of_forall_unit_power_classes
    {K : Type*} [Field K] [NumberField K] (a b : Kˣ)
    (h : ∀ n : ℕ+, ∃ u v : (ZMod (n : ℕ))ˣ, ∃ d : Kˣ,
      b ^ (u : ZMod (n : ℕ)).val =
        a ^ (v : ZMod (n : ℕ)).val * d ^ (n : ℕ)) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  apply numberField_zpowers_eq_of_forall_sup_prime_powers_eq a b
  intro p hp r
  let n : ℕ+ := ⟨p ^ r, pow_pos hp.pos r⟩
  obtain ⟨u, v, d, hd⟩ := h n
  exact zpowers_sup_power_range_eq_of_coprime_power_relation a b d (p ^ r)
    (u : ZMod (n : ℕ)).val (v : ZMod (n : ℕ)).val
    (ZMod.val_coe_unit_coprime u) (ZMod.val_coe_unit_coprime v) hd

end AnabelianGeometry.KummerTheory
