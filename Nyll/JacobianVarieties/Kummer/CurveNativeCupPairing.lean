/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicCup
public import Nyll.EtaleCohomology.Classical.AdicCupH0
public import Nyll.EtaleCohomology.Classical.AdicH0Comparison
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalAdicCup
public import Nyll.JacobianVarieties.Kummer.CurveNativeAdicH2
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Actual cup and degree pairings for a curve

Composing the original integral and rational cup products with the native
H² degree map defines the actual degree pairings. The original degree-zero
comparison takes the actual cup unit to one, so the pairings in degrees
(0,2) and (2,0) are perfect. Their duality maps are the actual cup followed
by native degree, with explicit inverses evaluating on a normalized H²
class or on the original degree-zero unit coordinate.

These edge dualities do not assert degree-one duality or positive-degree
graded commutativity. They retain the same curve model and coherent roots
as the native degree comparison used in arithmetic calculations.
-/

@[expose] public section

universe u

noncomputable section

open EtaleCohomology.Classical
open scoped TensorProduct

namespace AlgebraicCurve.CurveModel

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The original integral cup followed by the native H² degree map. -/
def nativeEllAdicCupPairing (i j : ℕ) (h : i + j = 2) :
    ellAdicCohomology M.C ℓ i →ₗ[ℤ_[ℓ]]
      ellAdicCohomology M.C ℓ j →ₗ[ℤ_[ℓ]] ℤ_[ℓ] :=
  (ellAdicCup M.C ℓ i j 2 h).compr₂ₛₗ (M.nativeEllAdicH2DegreeEquiv ℓ hℓ).toLinearMap

/-- The integral pairing retains the actual cup and native degree. -/
theorem nativeEllAdicCupPairing_apply (i j : ℕ) (h : i + j = 2)
    (x : ellAdicCohomology M.C ℓ i) (y : ellAdicCohomology M.C ℓ j) :
    M.nativeEllAdicCupPairing ℓ hℓ i j h x y =
      M.nativeEllAdicH2DegreeEquiv ℓ hℓ (ellAdicCup M.C ℓ i j 2 h x y) := rfl

/-- Integral degree pairing with H⁰ on the left is multiplication
of the original scalar coordinate and original H² degree. -/
theorem nativeEllAdicCupPairing_zero_two
    (x : ellAdicCohomology M.C ℓ 0) (y : ellAdicCohomology M.C ℓ 2) :
    M.nativeEllAdicCupPairing ℓ hℓ 0 2 rfl x y =
      ellAdicH0LinearEquiv M.C ℓ x * M.nativeEllAdicH2DegreeEquiv ℓ hℓ y := by
  rw [nativeEllAdicCupPairing_apply, ellAdicCup_zero_left, map_smul, smul_eq_mul]

/-- Integral degree pairing with H⁰ on the right has the same
original degree and scalar coordinates. -/
theorem nativeEllAdicCupPairing_two_zero
    (x : ellAdicCohomology M.C ℓ 2) (y : ellAdicCohomology M.C ℓ 0) :
    M.nativeEllAdicCupPairing ℓ hℓ 2 0 rfl x y =
      M.nativeEllAdicH2DegreeEquiv ℓ hℓ x * ellAdicH0LinearEquiv M.C ℓ y := by
  rw [nativeEllAdicCupPairing_apply, ellAdicCup_zero_right, map_smul, smul_eq_mul, mul_comm]

/-- The original rational cup followed by the native H² degree map. -/
def nativeRationalEllAdicCupPairing (i j : ℕ) (h : i + j = 2) :
    rationalEllAdicCohomology ℓ M.C i →ₗ[ℚ_[ℓ]]
      rationalEllAdicCohomology ℓ M.C j →ₗ[ℚ_[ℓ]] ℚ_[ℓ] :=
  (rationalEllAdicCup M.C ℓ i j 2 h).compr₂ₛₗ
    (M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).toLinearMap

/-- The rational pairing retains the actual cup and native degree. -/
theorem nativeRationalEllAdicCupPairing_apply (i j : ℕ) (h : i + j = 2)
    (x : rationalEllAdicCohomology ℓ M.C i) (y : rationalEllAdicCohomology ℓ M.C j) :
    M.nativeRationalEllAdicCupPairing ℓ hℓ i j h x y =
      M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        (rationalEllAdicCup M.C ℓ i j 2 h x y) := rfl

/-- On original pure tensors, rational degree pairing is scalar
extension of the original integral degree pairing. -/
theorem nativeRationalEllAdicCupPairing_tmul (i j : ℕ) (h : i + j = 2)
    (r s : ℚ_[ℓ]) (x : ellAdicCohomology M.C ℓ i) (y : ellAdicCohomology M.C ℓ j) :
    M.nativeRationalEllAdicCupPairing ℓ hℓ i j h
        (r ⊗ₜ[ℤ_[ℓ]] x) (s ⊗ₜ[ℤ_[ℓ]] y) =
      M.nativeEllAdicCupPairing ℓ hℓ i j h x y • (r * s) := by
  have hcup := congrArg (M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ)
    (rationalEllAdicCup_tmul M.C ℓ i j 2 h r s x y)
  exact hcup.trans
    (M.nativeRationalEllAdicH2DegreeEquiv_tmul ℓ hℓ (r * s)
      (ellAdicCup M.C ℓ i j 2 h x y))

/-- The original rational degree-one pairing is the actual scalar
extension of the original integral degree-one pairing. -/
theorem nativeRationalEllAdicCupPairing_one_one_baseChange :
    M.nativeRationalEllAdicCupPairing ℓ hℓ 1 1 rfl =
      LinearMap.BilinForm.baseChange ℚ_[ℓ] (M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
      induction y using TensorProduct.inductionOn with
      | tmul s y =>
          exact (M.nativeRationalEllAdicCupPairing_tmul ℓ hℓ 1 1 rfl r s x y).trans
            (LinearMap.BilinForm.baseChange_tmul
              (M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl) r x s y).symm
      | add y y' hy hy' =>
          have hleft :=
            (M.nativeRationalEllAdicCupPairing ℓ hℓ 1 1 rfl (r ⊗ₜ[ℤ_[ℓ]] x)).map_add y y'
          have hright :=
            (LinearMap.BilinForm.baseChange ℚ_[ℓ]
              (M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl) (r ⊗ₜ[ℤ_[ℓ]] x)).map_add y y'
          exact hleft.trans ((congrArg₂ (· + ·) hy hy').trans hright.symm)
  | add x x' hx hx' =>
      have hleft := LinearMap.congr_fun
        ((M.nativeRationalEllAdicCupPairing ℓ hℓ 1 1 rfl).map_add x x') y
      have hright := LinearMap.congr_fun
        ((LinearMap.BilinForm.baseChange ℚ_[ℓ]
          (M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl)).map_add x x') y
      exact hleft.trans ((congrArg₂ (· + ·) hx hx').trans hright.symm)

/-- Rational degree pairing with H⁰ on the left is multiplication
of the original scalar coordinate and original H² degree. -/
theorem nativeRationalEllAdicCupPairing_zero_two
    (x : rationalEllAdicCohomology ℓ M.C 0) (y : rationalEllAdicCohomology ℓ M.C 2) :
    M.nativeRationalEllAdicCupPairing ℓ hℓ 0 2 rfl x y =
      rationalEllAdicH0LinearEquiv M.C ℓ x * M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ y := by
  rw [nativeRationalEllAdicCupPairing_apply, rationalEllAdicCup_zero_left,
    map_smul, smul_eq_mul]

/-- Rational degree pairing with H⁰ on the right has the same
original degree and scalar coordinates. -/
theorem nativeRationalEllAdicCupPairing_two_zero
    (x : rationalEllAdicCohomology ℓ M.C 2) (y : rationalEllAdicCohomology ℓ M.C 0) :
    M.nativeRationalEllAdicCupPairing ℓ hℓ 2 0 rfl x y =
      M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ x * rationalEllAdicH0LinearEquiv M.C ℓ y := by
  rw [nativeRationalEllAdicCupPairing_apply, rationalEllAdicCup_zero_right,
    map_smul, smul_eq_mul, mul_comm]

/-- Actual cup followed by native degree gives perfect duality between
the original rational H⁰ and H², with H⁰ as the source of the duality map. -/
def nativeRationalEllAdicCupZeroTwoDuality :
    rationalEllAdicCohomology ℓ M.C 0 ≃ₗ[ℚ_[ℓ]]
      Module.Dual ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 2) := by
  let e0 : rationalEllAdicCohomology ℓ M.C 0 ≃ₗ[ℚ_[ℓ]] ℚ_[ℓ] :=
    rationalEllAdicH0LinearEquiv M.C ℓ
  let e2 : rationalEllAdicCohomology ℓ M.C 2 ≃ₗ[ℚ_[ℓ]] ℚ_[ℓ] :=
    M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
  let p := M.nativeRationalEllAdicCupPairing ℓ hℓ 0 2 rfl
  refine
    { __ := p
      invFun := fun φ => e0.symm (φ (e2.symm 1))
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    apply e0.injective
    rw [LinearEquiv.apply_symm_apply]
    change M.nativeRationalEllAdicCupPairing ℓ hℓ 0 2 rfl x (e2.symm 1) = e0 x
    rw [nativeRationalEllAdicCupPairing_zero_two]
    change e0 x * e2 (e2.symm 1) = e0 x
    rw [LinearEquiv.apply_symm_apply, mul_one]
  · intro φ
    apply LinearMap.ext
    intro y
    have hy : e2 y • e2.symm 1 = y := by
      apply e2.injective
      rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
    calc
      p (e0.symm (φ (e2.symm 1))) y = φ (e2.symm 1) * e2 y := by
        rw [nativeRationalEllAdicCupPairing_zero_two]
        change e0 (e0.symm (φ (e2.symm 1))) * e2 y = _
        rw [LinearEquiv.apply_symm_apply]
      _ = e2 y • φ (e2.symm 1) := mul_comm _ _
      _ = φ (e2 y • e2.symm 1) := (φ.map_smul (e2 y) (e2.symm 1)).symm
      _ = φ y := congrArg φ hy

/-- The first edge duality is the original cup followed by native degree. -/
theorem nativeRationalEllAdicCupZeroTwoDuality_apply
    (x : rationalEllAdicCohomology ℓ M.C 0) (y : rationalEllAdicCohomology ℓ M.C 2) :
    M.nativeRationalEllAdicCupZeroTwoDuality ℓ hℓ x y =
      M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        (rationalEllAdicCup M.C ℓ 0 2 2 rfl x y) := rfl

/-- Its inverse evaluates the original functional on the native H²
class of degree one, then returns the original H⁰ class of that scalar. -/
theorem nativeRationalEllAdicCupZeroTwoDuality_symm_apply
    (φ : Module.Dual ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 2)) :
    (M.nativeRationalEllAdicCupZeroTwoDuality ℓ hℓ).symm φ =
      (rationalEllAdicH0LinearEquiv M.C ℓ).symm
        (φ ((M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm 1)) := rfl

/-- Actual cup followed by native degree gives perfect duality between
the original rational H² and H⁰, with H² as the source of the duality map. -/
def nativeRationalEllAdicCupTwoZeroDuality :
    rationalEllAdicCohomology ℓ M.C 2 ≃ₗ[ℚ_[ℓ]]
      Module.Dual ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 0) := by
  let e0 : rationalEllAdicCohomology ℓ M.C 0 ≃ₗ[ℚ_[ℓ]] ℚ_[ℓ] :=
    rationalEllAdicH0LinearEquiv M.C ℓ
  let e2 : rationalEllAdicCohomology ℓ M.C 2 ≃ₗ[ℚ_[ℓ]] ℚ_[ℓ] :=
    M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
  let p := M.nativeRationalEllAdicCupPairing ℓ hℓ 2 0 rfl
  refine
    { __ := p
      invFun := fun φ => e2.symm (φ (e0.symm 1))
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    apply e2.injective
    rw [LinearEquiv.apply_symm_apply]
    change M.nativeRationalEllAdicCupPairing ℓ hℓ 2 0 rfl x (e0.symm 1) = e2 x
    rw [nativeRationalEllAdicCupPairing_two_zero]
    change e2 x * e0 (e0.symm 1) = e2 x
    rw [LinearEquiv.apply_symm_apply, mul_one]
  · intro φ
    apply LinearMap.ext
    intro y
    have hy : e0 y • e0.symm 1 = y := by
      apply e0.injective
      rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
    calc
      p (e2.symm (φ (e0.symm 1))) y = φ (e0.symm 1) * e0 y := by
        rw [nativeRationalEllAdicCupPairing_two_zero]
        change e2 (e2.symm (φ (e0.symm 1))) * e0 y = _
        rw [LinearEquiv.apply_symm_apply]
      _ = e0 y • φ (e0.symm 1) := mul_comm _ _
      _ = φ (e0 y • e0.symm 1) := (φ.map_smul (e0 y) (e0.symm 1)).symm
      _ = φ y := congrArg φ hy

/-- The second edge duality is the original cup followed by native degree. -/
theorem nativeRationalEllAdicCupTwoZeroDuality_apply
    (x : rationalEllAdicCohomology ℓ M.C 2) (y : rationalEllAdicCohomology ℓ M.C 0) :
    M.nativeRationalEllAdicCupTwoZeroDuality ℓ hℓ x y =
      M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        (rationalEllAdicCup M.C ℓ 2 0 2 rfl x y) := rfl

/-- Its inverse evaluates the original functional on the original H⁰
class of one, then returns the native H² class of that degree. -/
theorem nativeRationalEllAdicCupTwoZeroDuality_symm_apply
    (φ : Module.Dual ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 0)) :
    (M.nativeRationalEllAdicCupTwoZeroDuality ℓ hℓ).symm φ =
      (M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm
        (φ ((rationalEllAdicH0LinearEquiv M.C ℓ).symm 1)) := rfl

/-- Pairing the actual rational cup unit with the actual rational
class of an original divisor gives its original degree. -/
theorem nativeRationalEllAdicCupPairing_unit_divisor (D : Divisor K F) :
    M.nativeRationalEllAdicCupPairing ℓ hℓ 0 2 rfl (rationalEllAdicCupUnit M.C ℓ)
        ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] M.nativeEllAdicDivisorClass ℓ hℓ D) =
      (Divisor.degree D : ℚ_[ℓ]) := by
  have hunit := congrArg (M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ)
    (rationalEllAdicCup_unit_left M.C ℓ 2
      ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] M.nativeEllAdicDivisorClass ℓ hℓ D))
  exact hunit.trans (M.nativeRationalEllAdicH2DegreeEquiv_divisor ℓ hℓ D)

end AlgebraicCurve.CurveModel
