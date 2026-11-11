/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AdicH0Comparison
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ConstantH0Comparison
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Naturality of the original connected adic H0 comparison

The original finite constant-section comparison commutes with actual
pullback between arbitrary connected schemes. Equality at every actual
residue proves the same statement for the original integral comparison;
scalar extension proves it for the original rational comparison.
The two connected schemes need not coincide.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleCohomology.Classical

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
  (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y)

/-- The actual connected integral H0 coordinates retain the original
pullback between distinct connected schemes. -/
theorem ellAdicH0LinearEquiv_pullback (a : ellAdicCohomology Y ℓ 0) :
    ellAdicH0LinearEquiv X ℓ (ellAdicCohomologyPullback ℓ f 0 a) =
      ellAdicH0LinearEquiv Y ℓ a := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  cases n with
  | zero =>
      have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero ℓ)
      exact Subsingleton.elim _ _
  | succ n =>
      rw [ellAdicH0LinearEquiv_reduction, ellAdicH0LinearEquiv_reduction]
      change (constantH0Equiv X (ellPowerCoefficients ℓ n)
        (finiteLevelCohomologyPullback ℓ f n 0 (a.val n))).down =
          (constantH0Equiv Y (ellPowerCoefficients ℓ n) (a.val n)).down
      rw [finiteLevelCohomologyPullback_apply]
      exact congrArg ULift.down (constantH0Equiv_pullback f (ellPowerCoefficients ℓ n) (a.val n))

/-- The original rational H0 coordinate is natural under every actual
map between connected schemes, after the original scalar extension. -/
theorem rationalEllAdicH0LinearEquiv_pullback (a : rationalEllAdicCohomology ℓ Y 0) :
    rationalEllAdicH0LinearEquiv X ℓ (rationalEllAdicCohomologyPullback ℓ f 0 a) =
      rationalEllAdicH0LinearEquiv Y ℓ a := by
  induction a using TensorProduct.inductionOn with
  | tmul q a =>
      rw [rationalEllAdicCohomologyPullback_tmul]
      change ellAdicH0LinearEquiv X ℓ (ellAdicCohomologyPullback ℓ f 0 a) • q =
        ellAdicH0LinearEquiv Y ℓ a • q
      rw [ellAdicH0LinearEquiv_pullback]
  | add a b ha hb =>
      let F : rationalEllAdicCohomology ℓ Y 0 →ₗ[ℚ_[ℓ]] ℚ_[ℓ] :=
        (rationalEllAdicH0LinearEquiv X ℓ).toLinearMap.comp
          (rationalEllAdicCohomologyPullback ℓ f 0)
      let G : rationalEllAdicCohomology ℓ Y 0 →ₗ[ℚ_[ℓ]] ℚ_[ℓ] :=
        (rationalEllAdicH0LinearEquiv Y ℓ).toLinearMap
      exact (F.map_add a b).trans
        ((congrArg₂ (fun x y : ℚ_[ℓ] => x + y) ha hb).trans (G.map_add a b).symm)

end EtaleCohomology.Classical
