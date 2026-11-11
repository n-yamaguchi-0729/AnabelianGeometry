/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicCup
public import Nyll.EtaleCohomology.Classical.CupH1Anticommutativity
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalAdicCup
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Anticommutativity and alternating cup on original adic cohomology

The proved native degree-one sign passes through the original finite
coefficient comparison, the original integral compatible families, and
the original rational scalar extension. Rational degree-one self-cup
vanishes because two is invertible in the original rational coefficient
field, including when the prime is two.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry
open scoped TensorProduct

namespace EtaleCohomology.Classical

variable (X : Scheme.{u}) (ℓ : ℕ)

/-- The actual finite-level cup anticommutes in bidegree `(1,1)` at
every original coefficient level. -/
theorem finiteLevelCup_anticomm_one (n : ℕ)
    (x y : finiteLevelCohomology X ℓ n 1) :
    finiteLevelCup X ℓ n 1 1 2 rfl x y = -finiteLevelCup X ℓ n 1 1 2 rfl y x := by
  rw [finiteLevelCup_apply, finiteLevelCup_apply,
    etaleCohomologyCup_anticomm_one, map_neg]

variable [Fact ℓ.Prime]

/-- The actual original integral adic cup anticommutes in degree one. -/
theorem ellAdicCup_anticomm_one (x y : ellAdicCohomology X ℓ 1) :
    ellAdicCup X ℓ 1 1 2 rfl x y = -ellAdicCup X ℓ 1 1 2 rfl y x := by
  apply ellAdicCohomology_ext X ℓ 2
  intro n
  exact finiteLevelCup_anticomm_one X ℓ n (x.val n) (y.val n)

/-- The actual original rational adic cup anticommutes in degree one. -/
theorem rationalEllAdicCup_anticomm_one
    (x y : rationalEllAdicCohomology ℓ X 1) :
    rationalEllAdicCup X ℓ 1 1 2 rfl x y =
      -rationalEllAdicCup X ℓ 1 1 2 rfl y x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
      induction y using TensorProduct.inductionOn with
      | tmul s y =>
          rw [rationalEllAdicCup_tmul, rationalEllAdicCup_tmul,
            ellAdicCup_anticomm_one, TensorProduct.tmul_neg, mul_comm r s]
          rfl
      | add y y' hy hy' =>
          let F : rationalEllAdicCohomology ℓ X 1 →ₗ[ℚ_[ℓ]]
              rationalEllAdicCohomology ℓ X 2 :=
            rationalEllAdicCup X ℓ 1 1 2 rfl (r ⊗ₜ[ℤ_[ℓ]] x)
          let G : rationalEllAdicCohomology ℓ X 1 →ₗ[ℚ_[ℓ]]
              rationalEllAdicCohomology ℓ X 2 :=
            -((rationalEllAdicCup X ℓ 1 1 2 rfl).flip (r ⊗ₜ[ℤ_[ℓ]] x))
          exact (F.map_add y y').trans
            ((congrArg₂ (fun u v : rationalEllAdicCohomology ℓ X 2 => u + v)
              hy hy').trans (G.map_add y y').symm)
  | add x x' hx hx' =>
      let F : rationalEllAdicCohomology ℓ X 1 →ₗ[ℚ_[ℓ]]
          rationalEllAdicCohomology ℓ X 2 :=
        (rationalEllAdicCup X ℓ 1 1 2 rfl).flip y
      let G : rationalEllAdicCohomology ℓ X 1 →ₗ[ℚ_[ℓ]]
          rationalEllAdicCohomology ℓ X 2 :=
        -(rationalEllAdicCup X ℓ 1 1 2 rfl y)
      exact (F.map_add x x').trans
        ((congrArg₂ (fun u v : rationalEllAdicCohomology ℓ X 2 => u + v)
          hx hx').trans (G.map_add x x').symm)

/-- The actual degree-one rational cup is alternating, with no
restriction excluding the prime two. -/
theorem rationalEllAdicCup_self_one
    (x : rationalEllAdicCohomology ℓ X 1) :
    rationalEllAdicCup X ℓ 1 1 2 rfl x x = 0 := by
  have hsum := eq_neg_iff_add_eq_zero.mp (rationalEllAdicCup_anticomm_one X ℓ x x)
  have htwo : (2 : ℚ_[ℓ]) • rationalEllAdicCup X ℓ 1 1 2 rfl x x = 0 := by
    rw [two_smul]
    exact hsum
  have h := congrArg (fun z : rationalEllAdicCohomology ℓ X 2 => (2 : ℚ_[ℓ])⁻¹ • z) htwo
  simpa only [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : ℚ_[ℓ]) ≠ 0),
    one_smul, smul_zero] using h

end EtaleCohomology.Classical
