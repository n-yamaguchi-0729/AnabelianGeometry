/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicCup
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Cup on the original rational adic cohomology

Scalar extension of the actual integral cup gives a bilinear cup on
`ℚ_[ℓ] ⊗[ℤ_[ℓ]] Hⁱ(X, ℤ_[ℓ])`, the existing rational cohomology object.
The canonical tensor comparison computes the product on pure tensors.
Tensor induction then proves associativity and the two unit laws.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry
open scoped TensorProduct

namespace EtaleCohomology.Classical

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- Scalar extension of the original integral cup, on the existing
rational adic cohomology objects. -/
def rationalEllAdicCup (a b c : ℕ) (h : a + b = c) :
    rationalEllAdicCohomology ℓ X a →ₗ[ℚ_[ℓ]]
      rationalEllAdicCohomology ℓ X b →ₗ[ℚ_[ℓ]] rationalEllAdicCohomology ℓ X c :=
  TensorProduct.curry
    (((TensorProduct.lift (ellAdicCup X ℓ a b c h)).baseChange ℚ_[ℓ]).comp
      (TensorProduct.AlgebraTensorModule.distribBaseChange ℤ_[ℓ] ℚ_[ℓ]
        (ellAdicCohomology X ℓ a) (ellAdicCohomology X ℓ b)).symm.toLinearMap)

/-- On pure tensors, rational cup multiplies their scalars and cups their
original integral cohomology classes. -/
theorem rationalEllAdicCup_tmul (a b c : ℕ) (h : a + b = c)
    (r s : ℚ_[ℓ]) (x : ellAdicCohomology X ℓ a) (y : ellAdicCohomology X ℓ b) :
    rationalEllAdicCup X ℓ a b c h (r ⊗ₜ[ℤ_[ℓ]] x) (s ⊗ₜ[ℤ_[ℓ]] y) =
      (r * s) ⊗ₜ[ℤ_[ℓ]] ellAdicCup X ℓ a b c h x y := by
  change (TensorProduct.lift (ellAdicCup X ℓ a b c h)).baseChange ℚ_[ℓ]
      ((TensorProduct.AlgebraTensorModule.distribBaseChange ℤ_[ℓ] ℚ_[ℓ]
        (ellAdicCohomology X ℓ a) (ellAdicCohomology X ℓ b)).symm
          ((r ⊗ₜ[ℤ_[ℓ]] x) ⊗ₜ[ℚ_[ℓ]] (s ⊗ₜ[ℤ_[ℓ]] y))) = _
  rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
    LinearMap.baseChange_tmul, TensorProduct.lift.tmul]

/-- Associativity of the original rational adic cup product. -/
theorem rationalEllAdicCup_assoc
    (a b c ab bc abc : ℕ) (hab : a + b = ab) (hbc : b + c = bc)
    (habc : a + b + c = abc)
    (x : rationalEllAdicCohomology ℓ X a) (y : rationalEllAdicCohomology ℓ X b)
    (z : rationalEllAdicCohomology ℓ X c) :
    rationalEllAdicCup X ℓ ab c abc (by omega)
        (rationalEllAdicCup X ℓ a b ab hab x y) z =
      rationalEllAdicCup X ℓ a bc abc (by omega) x
        (rationalEllAdicCup X ℓ b c bc hbc y z) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
      induction y using TensorProduct.inductionOn with
      | tmul s y =>
          induction z using TensorProduct.inductionOn with
          | tmul t z =>
              simp only [rationalEllAdicCup_tmul,
                ellAdicCup_assoc X ℓ a b c ab bc abc hab hbc habc, mul_assoc]
              rfl
          | add z z' hz hz' =>
              let F : rationalEllAdicCohomology ℓ X c →ₗ[ℚ_[ℓ]]
                  rationalEllAdicCohomology ℓ X abc :=
                rationalEllAdicCup X ℓ ab c abc (by omega)
                  (rationalEllAdicCup X ℓ a b ab hab
                    (r ⊗ₜ[ℤ_[ℓ]] x) (s ⊗ₜ[ℤ_[ℓ]] y))
              let G : rationalEllAdicCohomology ℓ X c →ₗ[ℚ_[ℓ]]
                  rationalEllAdicCohomology ℓ X abc :=
                (rationalEllAdicCup X ℓ a bc abc (by omega)
                  (r ⊗ₜ[ℤ_[ℓ]] x)).comp
                    (rationalEllAdicCup X ℓ b c bc hbc (s ⊗ₜ[ℤ_[ℓ]] y))
              exact (F.map_add z z').trans
                ((congrArg₂ (fun u v : rationalEllAdicCohomology ℓ X abc => u + v)
                  hz hz').trans (G.map_add z z').symm)
      | add y y' hy hy' =>
          let F : rationalEllAdicCohomology ℓ X b →ₗ[ℚ_[ℓ]]
              rationalEllAdicCohomology ℓ X abc :=
            ((rationalEllAdicCup X ℓ ab c abc (by omega)).flip z).comp
              (rationalEllAdicCup X ℓ a b ab hab (r ⊗ₜ[ℤ_[ℓ]] x))
          let G : rationalEllAdicCohomology ℓ X b →ₗ[ℚ_[ℓ]]
              rationalEllAdicCohomology ℓ X abc :=
            (rationalEllAdicCup X ℓ a bc abc (by omega) (r ⊗ₜ[ℤ_[ℓ]] x)).comp
              ((rationalEllAdicCup X ℓ b c bc hbc).flip z)
          exact (F.map_add y y').trans
            ((congrArg₂ (fun u v : rationalEllAdicCohomology ℓ X abc => u + v)
              hy hy').trans (G.map_add y y').symm)
  | add x x' hx hx' =>
      let F : rationalEllAdicCohomology ℓ X a →ₗ[ℚ_[ℓ]]
          rationalEllAdicCohomology ℓ X abc :=
        ((rationalEllAdicCup X ℓ ab c abc (by omega)).flip z).comp
          ((rationalEllAdicCup X ℓ a b ab hab).flip y)
      let G : rationalEllAdicCohomology ℓ X a →ₗ[ℚ_[ℓ]]
          rationalEllAdicCohomology ℓ X abc :=
        (rationalEllAdicCup X ℓ a bc abc (by omega)).flip
          (rationalEllAdicCup X ℓ b c bc hbc y z)
      exact (F.map_add x x').trans
        ((congrArg₂ (fun u v : rationalEllAdicCohomology ℓ X abc => u + v)
          hx hx').trans (G.map_add x x').symm)

/-- The original integral cup unit, extended to rational coefficients. -/
def rationalEllAdicCupUnit : rationalEllAdicCohomology ℓ X 0 :=
  (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] ellAdicCupUnit X ℓ

/-- The rational cup unit acts on the left. -/
theorem rationalEllAdicCup_unit_left (i : ℕ) (x : rationalEllAdicCohomology ℓ X i) :
    rationalEllAdicCup X ℓ 0 i i (zero_add i) (rationalEllAdicCupUnit X ℓ) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
      simp only [rationalEllAdicCupUnit, rationalEllAdicCup_tmul,
        one_mul, ellAdicCup_unit_left]
      rfl
  | add x y hx hy =>
      let F : rationalEllAdicCohomology ℓ X i →ₗ[ℚ_[ℓ]]
          rationalEllAdicCohomology ℓ X i :=
        rationalEllAdicCup X ℓ 0 i i (zero_add i) (rationalEllAdicCupUnit X ℓ)
      exact (F.map_add x y).trans
        (congrArg₂ (fun u v : rationalEllAdicCohomology ℓ X i => u + v) hx hy)

/-- The rational cup unit acts on the right. -/
theorem rationalEllAdicCup_unit_right (i : ℕ) (x : rationalEllAdicCohomology ℓ X i) :
    rationalEllAdicCup X ℓ i 0 i (add_zero i) x (rationalEllAdicCupUnit X ℓ) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
      simp only [rationalEllAdicCupUnit, rationalEllAdicCup_tmul,
        mul_one, ellAdicCup_unit_right]
      rfl
  | add x y hx hy =>
      let F : rationalEllAdicCohomology ℓ X i →ₗ[ℚ_[ℓ]]
          rationalEllAdicCohomology ℓ X i :=
        (rationalEllAdicCup X ℓ i 0 i (add_zero i)).flip (rationalEllAdicCupUnit X ℓ)
      exact (F.map_add x y).trans
        (congrArg₂ (fun u v : rationalEllAdicCohomology ℓ X i => u + v) hx hy)

end EtaleCohomology.Classical
