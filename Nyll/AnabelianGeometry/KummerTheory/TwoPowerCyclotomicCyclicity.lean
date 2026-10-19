/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.Index

/-! # Cyclicity of good 2-primary cyclotomic characters -/

namespace AnabelianGeometry.KummerTheory

/-- Units congruent to one modulo four form a cyclic group. -/
theorem isCyclic_twoPower_unitsMap_four_ker
    (n : ℕ) (h4 : 4 ∣ 2 ^ (n + 2)) :
    IsCyclic (ZMod.unitsMap h4).ker := by
  let : NeZero (2 ^ (n + 2)) := ⟨pow_ne_zero _ (by decide)⟩
  let f : (ZMod (2 ^ (n + 2)))ˣ →* (ZMod 4)ˣ := ZMod.unitsMap h4
  change IsCyclic f.ker
  have hf : Function.Surjective f := ZMod.unitsMap_surjective h4
  have hfour : Nat.card (ZMod 4)ˣ = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    decide
  have hbig : Nat.card (ZMod (2 ^ (n + 2)))ˣ = 2 ^ (n + 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    simpa [Nat.add_assoc] using
      Nat.totient_prime_pow_succ Nat.prime_two (n + 1)
  have hcard : Nat.card f.ker = 2 ^ n := by
    have h := f.ker.card_mul_index
    rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
      Subgroup.card_top, hfour, hbig] at h
    have hpow := pow_succ 2 n
    omega
  have hfive : Nat.Coprime 5 (2 ^ (n + 2)) :=
    (by decide : Nat.Coprime 5 2).pow_right _
  let v : (ZMod (2 ^ (n + 2)))ˣ := ZMod.unitOfCoprime 5 hfive
  have hv : (v : ZMod (2 ^ (n + 2))) = 5 := by simp [v]
  have hfv : f v = 1 := by
    apply Units.ext
    change (ZMod.castHom h4 (ZMod 4)) (v : ZMod (2 ^ (n + 2))) = 1
    calc
      (ZMod.castHom h4 (ZMod 4)) (v : ZMod (2 ^ (n + 2))) =
          (ZMod.castHom h4 (ZMod 4)) (5 : ZMod (2 ^ (n + 2))) := congrArg _ hv
      _ = (5 : ZMod 4) := map_natCast _ 5
      _ = 1 := by decide
  have hvorder : orderOf v = 2 ^ n := by
    rw [← orderOf_injective _ Units.coeHom_injective v, Units.coeHom_apply, hv]
    exact ZMod.orderOf_five n
  let w : f.ker := ⟨v, hfv⟩
  apply isCyclic_iff_exists_orderOf_eq_natCard.mpr
  refine ⟨w, ?_⟩
  rw [← orderOf_injective f.ker.subtype Subtype.val_injective w]
  change orderOf v = Nat.card f.ker
  rw [hvorder, hcard]

/-- A faithful cyclotomic character fixing fourth roots has cyclic source. -/
theorem isCyclic_of_injective_twoPower_character
    {G : Type*} [Group G]
    (n : ℕ) (h4 : 4 ∣ 2 ^ (n + 2))
    (χ : G →* (ZMod (2 ^ (n + 2)))ˣ)
    (hχ : Function.Injective χ)
    (hgood : ∀ g, ZMod.unitsMap h4 (χ g) = 1) :
    IsCyclic G := by
  let f : (ZMod (2 ^ (n + 2)))ˣ →* (ZMod 4)ˣ := ZMod.unitsMap h4
  let : IsCyclic f.ker := isCyclic_twoPower_unitsMap_four_ker n h4
  let ψ : G →* f.ker :=
    { toFun := fun g => ⟨χ g, hgood g⟩
      map_one' := Subtype.ext χ.map_one
      map_mul' := fun g h => Subtype.ext (χ.map_mul g h) }
  apply isCyclic_of_injective ψ
  intro g h hgh
  apply hχ
  exact congrArg Subtype.val hgh

end AnabelianGeometry.KummerTheory
