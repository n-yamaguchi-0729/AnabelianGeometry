/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicCup
public import Nyll.EtaleCohomology.Classical.AdicH0Comparison
public import Nyll.EtaleCohomology.Classical.ConstantH0Comparison
public import Nyll.EtaleCohomology.Classical.CupH0Comparison
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalAdicCup
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Degree zero acts by the original adic scalars

The original connected H⁰ equivalences send the actual integral and
rational cup units to one. Every original H⁰ class is therefore its
original scalar times that unit. Cup with an H⁰ class on either side is
the original scalar action in every degree. This proves centrality in
degree zero; no positive-degree graded commutativity is asserted.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry
open scoped TensorProduct

namespace EtaleCohomology.Classical

variable (X : Scheme.{u}) [ConnectedSpace X] (ℓ : ℕ) [Fact ℓ.Prime]

/-- The original integral H⁰ comparison sends the actual cup unit to one. -/
theorem ellAdicH0LinearEquiv_cupUnit :
    ellAdicH0LinearEquiv X ℓ (ellAdicCupUnit X ℓ) = 1 := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  cases n with
  | zero =>
      have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero ℓ)
      exact Subsingleton.elim _ _
  | succ n =>
      calc
        _ = (constantH0Equiv X (ellPowerCoefficients ℓ n)
            (finiteLevelCupUnit X ℓ n)).down :=
          ellAdicH0LinearEquiv_reduction X ℓ (ellAdicCupUnit X ℓ) n
        _ = 1 := congrArg ULift.down (finiteLevelCupUnit_constantH0 X ℓ n)
        _ = _ := (map_one (PadicInt.toZModPow (n + 1))).symm

/-- The original rational H⁰ comparison is scalar extension of its
original integral comparison on each pure tensor. -/
theorem rationalEllAdicH0LinearEquiv_tmul (q : ℚ_[ℓ]) (a : ellAdicCohomology X ℓ 0) :
    rationalEllAdicH0LinearEquiv X ℓ (q ⊗ₜ[ℤ_[ℓ]] a) =
      ellAdicH0LinearEquiv X ℓ a • q := rfl

/-- The original rational H⁰ comparison sends the actual cup unit to one. -/
theorem rationalEllAdicH0LinearEquiv_cupUnit :
    rationalEllAdicH0LinearEquiv X ℓ (rationalEllAdicCupUnit X ℓ) = 1 := by
  rw [rationalEllAdicCupUnit, rationalEllAdicH0LinearEquiv_tmul,
    ellAdicH0LinearEquiv_cupUnit, one_smul]

/-- Every original integral H⁰ class is its original scalar times the
actual integral cup unit. -/
theorem ellAdicH0_eq_smul_unit (x : ellAdicCohomology X ℓ 0) :
    x = ellAdicH0LinearEquiv X ℓ x • ellAdicCupUnit X ℓ := by
  apply (ellAdicH0LinearEquiv X ℓ).injective
  rw [map_smul, ellAdicH0LinearEquiv_cupUnit, smul_eq_mul, mul_one]

/-- Every original rational H⁰ class is its original scalar times the
actual rational cup unit. -/
theorem rationalEllAdicH0_eq_smul_unit (x : rationalEllAdicCohomology ℓ X 0) :
    x = rationalEllAdicH0LinearEquiv X ℓ x • rationalEllAdicCupUnit X ℓ := by
  apply (rationalEllAdicH0LinearEquiv X ℓ).injective
  rw [map_smul, rationalEllAdicH0LinearEquiv_cupUnit, smul_eq_mul, mul_one]

/-- Integral cup with an original H⁰ class on the left is exactly its
original adic scalar action. -/
theorem ellAdicCup_zero_left (i : ℕ)
    (x : ellAdicCohomology X ℓ 0) (y : ellAdicCohomology X ℓ i) :
    ellAdicCup X ℓ 0 i i (zero_add i) x y = ellAdicH0LinearEquiv X ℓ x • y := by
  calc
    _ = ellAdicCup X ℓ 0 i i (zero_add i)
        (ellAdicH0LinearEquiv X ℓ x • ellAdicCupUnit X ℓ) y :=
      congrArg (fun z => ellAdicCup X ℓ 0 i i (zero_add i) z y)
        (ellAdicH0_eq_smul_unit X ℓ x)
    _ = _ := by
      rw [map_smul, LinearMap.smul_apply, ellAdicCup_unit_left]

/-- Integral cup with an original H⁰ class on the right is the same
original adic scalar action. -/
theorem ellAdicCup_zero_right (i : ℕ)
    (x : ellAdicCohomology X ℓ i) (y : ellAdicCohomology X ℓ 0) :
    ellAdicCup X ℓ i 0 i (add_zero i) x y = ellAdicH0LinearEquiv X ℓ y • x := by
  calc
    _ = ellAdicCup X ℓ i 0 i (add_zero i) x
        (ellAdicH0LinearEquiv X ℓ y • ellAdicCupUnit X ℓ) :=
      congrArg (fun z => ellAdicCup X ℓ i 0 i (add_zero i) x z)
        (ellAdicH0_eq_smul_unit X ℓ y)
    _ = _ := by
      rw [map_smul, ellAdicCup_unit_right]

/-- Original integral H⁰ classes are central for the actual cup. -/
theorem ellAdicCup_zero_comm (i : ℕ)
    (x : ellAdicCohomology X ℓ 0) (y : ellAdicCohomology X ℓ i) :
    ellAdicCup X ℓ 0 i i (zero_add i) x y =
      ellAdicCup X ℓ i 0 i (add_zero i) y x := by
  rw [ellAdicCup_zero_left, ellAdicCup_zero_right]

/-- Rational cup with an original H⁰ class on the left is exactly its
original adic-field scalar action. -/
theorem rationalEllAdicCup_zero_left (i : ℕ)
    (x : rationalEllAdicCohomology ℓ X 0) (y : rationalEllAdicCohomology ℓ X i) :
    rationalEllAdicCup X ℓ 0 i i (zero_add i) x y =
      rationalEllAdicH0LinearEquiv X ℓ x • y := by
  calc
    _ = rationalEllAdicCup X ℓ 0 i i (zero_add i)
        (rationalEllAdicH0LinearEquiv X ℓ x • rationalEllAdicCupUnit X ℓ) y :=
      congrArg (fun z => rationalEllAdicCup X ℓ 0 i i (zero_add i) z y)
        (rationalEllAdicH0_eq_smul_unit X ℓ x)
    _ = _ := by
      rw [map_smul, LinearMap.smul_apply, rationalEllAdicCup_unit_left]

/-- Rational cup with an original H⁰ class on the right is the same
original adic-field scalar action. -/
theorem rationalEllAdicCup_zero_right (i : ℕ)
    (x : rationalEllAdicCohomology ℓ X i) (y : rationalEllAdicCohomology ℓ X 0) :
    rationalEllAdicCup X ℓ i 0 i (add_zero i) x y =
      rationalEllAdicH0LinearEquiv X ℓ y • x := by
  calc
    _ = rationalEllAdicCup X ℓ i 0 i (add_zero i) x
        (rationalEllAdicH0LinearEquiv X ℓ y • rationalEllAdicCupUnit X ℓ) :=
      congrArg (fun z => rationalEllAdicCup X ℓ i 0 i (add_zero i) x z)
        (rationalEllAdicH0_eq_smul_unit X ℓ y)
    _ = _ := by
      rw [map_smul, rationalEllAdicCup_unit_right]

/-- Original rational H⁰ classes are central for the actual cup. -/
theorem rationalEllAdicCup_zero_comm (i : ℕ)
    (x : rationalEllAdicCohomology ℓ X 0) (y : rationalEllAdicCohomology ℓ X i) :
    rationalEllAdicCup X ℓ 0 i i (zero_add i) x y =
      rationalEllAdicCup X ℓ i 0 i (add_zero i) y x := by
  rw [rationalEllAdicCup_zero_left, rationalEllAdicCup_zero_right]

/-- In degree zero the original integral comparison takes actual cup
to multiplication of the original adic scalars. -/
theorem ellAdicH0LinearEquiv_cup (x y : ellAdicCohomology X ℓ 0) :
    ellAdicH0LinearEquiv X ℓ (ellAdicCup X ℓ 0 0 0 rfl x y) =
      ellAdicH0LinearEquiv X ℓ x * ellAdicH0LinearEquiv X ℓ y := by
  rw [ellAdicCup_zero_left, map_smul, smul_eq_mul]

/-- In degree zero the original rational comparison takes actual cup
to multiplication of the original adic-field scalars. -/
theorem rationalEllAdicH0LinearEquiv_cup (x y : rationalEllAdicCohomology ℓ X 0) :
    rationalEllAdicH0LinearEquiv X ℓ (rationalEllAdicCup X ℓ 0 0 0 rfl x y) =
      rationalEllAdicH0LinearEquiv X ℓ x * rationalEllAdicH0LinearEquiv X ℓ y := by
  rw [rationalEllAdicCup_zero_left, map_smul, smul_eq_mul]

end EtaleCohomology.Classical
