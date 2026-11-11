/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicCup
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.FiniteLevelCupPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalAdicCup
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Geometric pullback preserves the original adic cup

At each original finite level, the original pullback preserves cup and
the unit. Their compatible families prove the integral statements.
Scalar extension then proves the same statements for the original
rational adic cohomology and its original geometric pullback.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleCohomology.Classical

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Original integral pullback preserves cup on the original inverse limits. -/
theorem ellAdicCohomologyPullback_cup (a b c : ℕ) (h : a + b = c)
    (x : ellAdicCohomology Y ℓ a) (y : ellAdicCohomology Y ℓ b) :
    ellAdicCohomologyPullback ℓ f c (ellAdicCup Y ℓ a b c h x y) =
      ellAdicCup X ℓ a b c h
        (ellAdicCohomologyPullback ℓ f a x) (ellAdicCohomologyPullback ℓ f b y) := by
  apply ellAdicCohomology_ext X ℓ c
  intro n
  exact finiteLevelCohomologyPullback_cup ℓ f n a b c h (x.val n) (y.val n)

/-- Original integral pullback preserves the compatible cup unit. -/
theorem ellAdicCohomologyPullback_cupUnit :
    ellAdicCohomologyPullback ℓ f 0 (ellAdicCupUnit Y ℓ) = ellAdicCupUnit X ℓ := by
  apply ellAdicCohomology_ext X ℓ 0
  intro n
  exact finiteLevelCohomologyPullback_cupUnit ℓ f n

/-- Original rational pullback preserves cup on the original scalar extension. -/
theorem rationalEllAdicCohomologyPullback_cup (a b c : ℕ) (h : a + b = c)
    (x : rationalEllAdicCohomology ℓ Y a) (y : rationalEllAdicCohomology ℓ Y b) :
    rationalEllAdicCohomologyPullback ℓ f c (rationalEllAdicCup Y ℓ a b c h x y) =
      rationalEllAdicCup X ℓ a b c h
        (rationalEllAdicCohomologyPullback ℓ f a x)
        (rationalEllAdicCohomologyPullback ℓ f b y) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
      induction y using TensorProduct.inductionOn with
      | tmul s y =>
          simp only [rationalEllAdicCup_tmul, rationalEllAdicCohomologyPullback_tmul,
            ellAdicCohomologyPullback_cup]
          rfl
      | add y z hy hz =>
          let F : rationalEllAdicCohomology ℓ Y b →ₗ[ℚ_[ℓ]]
              rationalEllAdicCohomology ℓ X c :=
            (rationalEllAdicCohomologyPullback ℓ f c).comp
              (rationalEllAdicCup Y ℓ a b c h (r ⊗ₜ[ℤ_[ℓ]] x))
          let G : rationalEllAdicCohomology ℓ Y b →ₗ[ℚ_[ℓ]]
              rationalEllAdicCohomology ℓ X c :=
            (rationalEllAdicCup X ℓ a b c h
              (rationalEllAdicCohomologyPullback ℓ f a (r ⊗ₜ[ℤ_[ℓ]] x))).comp
                (rationalEllAdicCohomologyPullback ℓ f b)
          exact (F.map_add y z).trans
            ((congrArg₂ (fun u v : rationalEllAdicCohomology ℓ X c => u + v)
              hy hz).trans (G.map_add y z).symm)
  | add x z hx hz =>
      let F : rationalEllAdicCohomology ℓ Y a →ₗ[ℚ_[ℓ]]
          rationalEllAdicCohomology ℓ X c :=
        (rationalEllAdicCohomologyPullback ℓ f c).comp
          ((rationalEllAdicCup Y ℓ a b c h).flip y)
      let G : rationalEllAdicCohomology ℓ Y a →ₗ[ℚ_[ℓ]]
          rationalEllAdicCohomology ℓ X c :=
        ((rationalEllAdicCup X ℓ a b c h).flip
          (rationalEllAdicCohomologyPullback ℓ f b y)).comp
            (rationalEllAdicCohomologyPullback ℓ f a)
      exact (F.map_add x z).trans
        ((congrArg₂ (fun u v : rationalEllAdicCohomology ℓ X c => u + v)
          hx hz).trans (G.map_add x z).symm)

/-- Original rational pullback preserves the scalar-extended cup unit. -/
theorem rationalEllAdicCohomologyPullback_cupUnit :
    rationalEllAdicCohomologyPullback ℓ f 0 (rationalEllAdicCupUnit Y ℓ) =
      rationalEllAdicCupUnit X ℓ := by
  simp only [rationalEllAdicCupUnit, rationalEllAdicCohomologyPullback_tmul,
    ellAdicCohomologyPullback_cupUnit]
  rfl

end EtaleCohomology.Classical
