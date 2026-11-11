/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.AlgebraicallyClosedCohomology
public import Nyll.EtaleCohomology.Classical.ExternalCupPullbackComposition
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Original adic cohomology of a separably closed point

The existing vanishing for the original étale cohomology of a separably
closed field applies to every original finite coefficient group. It
therefore kills every coordinate of the original integral inverse limit
and every original rational tensor. A scheme map factoring through this
actual point induces zero on positive-degree rational cohomology.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleCohomology.Classical

variable (K : Type u) [Field K] [IsSepClosed K] (ℓ : ℕ)

/-- Each original finite coefficient cohomology group of an actual
separably closed point vanishes in positive degree. -/
theorem finiteLevelCohomology_eq_zero_of_isSepClosed (n i : ℕ)
    (a : finiteLevelCohomology (Spec (CommRingCat.of K)) ℓ n (i + 1)) : a = 0 :=
  fieldSheafCohomology_eq_zero_of_isSepClosed K
    ((constantSheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj
      (ellPowerCoefficients ℓ n)) i a

variable [Fact ℓ.Prime]

/-- The original compatible-family cohomology of a separably closed
point vanishes in positive degree, coordinate by coordinate. -/
theorem ellAdicCohomology_eq_zero_of_isSepClosed (i : ℕ)
    (a : ellAdicCohomology (Spec (CommRingCat.of K)) ℓ (i + 1)) : a = 0 := by
  apply ellAdicCohomology_ext (Spec (CommRingCat.of K)) ℓ (i + 1)
  intro n
  change a.val n = 0
  exact finiteLevelCohomology_eq_zero_of_isSepClosed K ℓ n i (a.val n)

/-- The original rational tensor cohomology of a separably closed
point vanishes in every positive degree. -/
theorem rationalEllAdicCohomology_eq_zero_of_isSepClosed (i : ℕ)
    (a : rationalEllAdicCohomology ℓ (Spec (CommRingCat.of K)) (i + 1)) : a = 0 := by
  induction a using TensorProduct.inductionOn with
  | tmul q a =>
      exact (congrArg
        (fun z : ellAdicCohomology (Spec (CommRingCat.of K)) ℓ (i + 1) =>
          q ⊗ₜ[ℤ_[ℓ]] z)
        (ellAdicCohomology_eq_zero_of_isSepClosed K ℓ i a)).trans
          (TensorProduct.tmul_zero (R := ℤ_[ℓ])
            (ellAdicCohomology (Spec (CommRingCat.of K)) ℓ (i + 1)) q)
  | add a b ha hb =>
      exact (congrArg₂
        (fun x y : ℚ_[ℓ] ⊗[ℤ_[ℓ]]
          ellAdicCohomology (Spec (CommRingCat.of K)) ℓ (i + 1) => x + y)
        ha hb).trans
          (zero_add (0 : ℚ_[ℓ] ⊗[ℤ_[ℓ]]
            ellAdicCohomology (Spec (CommRingCat.of K)) ℓ (i + 1)))

/-- Factoring a scheme map through an actual separably closed point
kills its original positive-degree rational cohomological pullback. -/
theorem rationalEllAdicCohomologyPullback_through_isSepClosed
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    (g : Spec (CommRingCat.of K) ⟶ Y) (i : ℕ) :
    rationalEllAdicCohomologyPullback ℓ (f ≫ g) (i + 1) = 0 := by
  apply LinearMap.ext
  intro a
  change rationalEllAdicCohomologyPullback ℓ (f ≫ g) (i + 1) a = 0
  rw [rationalEllAdicCohomologyPullback_comp, LinearMap.comp_apply,
    rationalEllAdicCohomology_eq_zero_of_isSepClosed K ℓ i
      (rationalEllAdicCohomologyPullback ℓ g (i + 1) a), map_zero]

end EtaleCohomology.Classical
