/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicCup
public import Nyll.EtaleCohomology.Classical.AdicCupPullback
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalAdicCup
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The actual rational external cup and Künneth map

The two original projections from the scheme fibre product pull classes
to the existing rational adic cohomology of that product. Their cup gives
a bilinear external product. The tensor universal property and the direct
sum over complementary degrees give the actual Künneth map in every total
degree. Its values on generators and its integral pure-tensor calculation
retain the original projections, inverse limits, and scalar extension.

This constructs the map. It does not assert its injectivity, surjectivity,
or the cohomological Künneth isomorphism.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open scoped DirectSum TensorProduct

namespace EtaleCohomology.Classical

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- External cup on original rational adic cohomology, using the two
original projections from the actual scheme fibre product. -/
def rationalEllAdicExternalCup (a b c : ℕ) (h : a + b = c) :
    rationalEllAdicCohomology ℓ X a →ₗ[ℚ_[ℓ]]
      rationalEllAdicCohomology ℓ Y b →ₗ[ℚ_[ℓ]]
        rationalEllAdicCohomology ℓ (pullback f g) c :=
  (rationalEllAdicCup (pullback f g) ℓ a b c h).compl₁₂
    (rationalEllAdicCohomologyPullback ℓ (pullback.fst f g) a)
    (rationalEllAdicCohomologyPullback ℓ (pullback.snd f g) b)

/-- The external product is the cup of the actual projection pullbacks. -/
theorem rationalEllAdicExternalCup_apply (a b c : ℕ) (h : a + b = c)
    (x : rationalEllAdicCohomology ℓ X a) (y : rationalEllAdicCohomology ℓ Y b) :
    rationalEllAdicExternalCup ℓ f g a b c h x y =
      rationalEllAdicCup (pullback f g) ℓ a b c h
        (rationalEllAdicCohomologyPullback ℓ (pullback.fst f g) a x)
        (rationalEllAdicCohomologyPullback ℓ (pullback.snd f g) b y) := rfl

/-- On extended integral classes, external cup retains the original
integral projection pullbacks and the original integral cup. -/
theorem rationalEllAdicExternalCup_tmul (a b c : ℕ) (h : a + b = c)
    (r s : ℚ_[ℓ]) (x : ellAdicCohomology X ℓ a) (y : ellAdicCohomology Y ℓ b) :
    rationalEllAdicExternalCup ℓ f g a b c h (r ⊗ₜ[ℤ_[ℓ]] x) (s ⊗ₜ[ℤ_[ℓ]] y) =
      (r * s) ⊗ₜ[ℤ_[ℓ]] ellAdicCup (pullback f g) ℓ a b c h
        (ellAdicCohomologyPullback ℓ (pullback.fst f g) a x)
        (ellAdicCohomologyPullback ℓ (pullback.snd f g) b y) := by
  exact (rationalEllAdicExternalCup_apply ℓ f g a b c h
    (r ⊗ₜ[ℤ_[ℓ]] x) (s ⊗ₜ[ℤ_[ℓ]] y)).trans
      ((congrArg₂
        (fun (u : rationalEllAdicCohomology ℓ (pullback f g) a)
            (v : rationalEllAdicCohomology ℓ (pullback f g) b) =>
          rationalEllAdicCup (pullback f g) ℓ a b c h u v)
        (rationalEllAdicCohomologyPullback_tmul ℓ (pullback.fst f g) a r x)
        (rationalEllAdicCohomologyPullback_tmul ℓ (pullback.snd f g) b s y)).trans
          (rationalEllAdicCup_tmul (pullback f g) ℓ a b c h r s
            (ellAdicCohomologyPullback ℓ (pullback.fst f g) a x)
            (ellAdicCohomologyPullback ℓ (pullback.snd f g) b y)))

/-- External cup with the first factor's unit is the second projection
pullback on the original rational cohomology. -/
theorem rationalEllAdicExternalCup_unit_left (i : ℕ)
    (y : rationalEllAdicCohomology ℓ Y i) :
    rationalEllAdicExternalCup ℓ f g 0 i i (zero_add i) (rationalEllAdicCupUnit X ℓ) y =
      rationalEllAdicCohomologyPullback ℓ (pullback.snd f g) i y := by
  rw [rationalEllAdicExternalCup_apply, rationalEllAdicCohomologyPullback_cupUnit,
    rationalEllAdicCup_unit_left]

/-- External cup with the second factor's unit is the first projection
pullback on the original rational cohomology. -/
theorem rationalEllAdicExternalCup_unit_right (i : ℕ)
    (x : rationalEllAdicCohomology ℓ X i) :
    rationalEllAdicExternalCup ℓ f g i 0 i (add_zero i) x (rationalEllAdicCupUnit Y ℓ) =
      rationalEllAdicCohomologyPullback ℓ (pullback.fst f g) i x := by
  rw [rationalEllAdicExternalCup_apply, rationalEllAdicCohomologyPullback_cupUnit,
    rationalEllAdicCup_unit_right]

/-- The actual Künneth map in one bidegree, obtained from the universal
property of the tensor product over the adic field. -/
def rationalEllAdicKunnethComponent (a b c : ℕ) (h : a + b = c) :
    (rationalEllAdicCohomology ℓ X a ⊗[ℚ_[ℓ]] rationalEllAdicCohomology ℓ Y b) →ₗ[ℚ_[ℓ]]
      rationalEllAdicCohomology ℓ (pullback f g) c :=
  TensorProduct.lift (rationalEllAdicExternalCup ℓ f g a b c h)

/-- On pure tensors, the Künneth component is the actual external cup. -/
theorem rationalEllAdicKunnethComponent_tmul (a b c : ℕ) (h : a + b = c)
    (x : rationalEllAdicCohomology ℓ X a) (y : rationalEllAdicCohomology ℓ Y b) :
    rationalEllAdicKunnethComponent ℓ f g a b c h (x ⊗ₜ[ℚ_[ℓ]] y) =
      rationalEllAdicExternalCup ℓ f g a b c h x y := rfl

/-- The full Künneth map in total degree `n`, with the original rational
cohomology tensor factors in every complementary pair of degrees. -/
def rationalEllAdicKunnethMap (n : ℕ) :
    (⨁ d : Fin (n + 1),
      rationalEllAdicCohomology ℓ X d.val ⊗[ℚ_[ℓ]]
        rationalEllAdicCohomology ℓ Y (n - d.val)) →ₗ[ℚ_[ℓ]]
      rationalEllAdicCohomology ℓ (pullback f g) n :=
  DirectSum.toModule ℚ_[ℓ] (Fin (n + 1)) (rationalEllAdicCohomology ℓ (pullback f g) n)
    (fun d => rationalEllAdicKunnethComponent ℓ f g d.val (n - d.val) n
      (Nat.add_sub_of_le (Nat.le_of_lt_succ d.isLt)))

/-- Every direct-sum pure tensor is sent to the cup of the original two
projection pullbacks. -/
theorem rationalEllAdicKunnethMap_lof_tmul (n : ℕ) (d : Fin (n + 1))
    (x : rationalEllAdicCohomology ℓ X d.val)
    (y : rationalEllAdicCohomology ℓ Y (n - d.val)) :
    rationalEllAdicKunnethMap ℓ f g n
        (DirectSum.lof ℚ_[ℓ] (Fin (n + 1))
          (fun j => rationalEllAdicCohomology ℓ X j.val ⊗[ℚ_[ℓ]]
            rationalEllAdicCohomology ℓ Y (n - j.val)) d (x ⊗ₜ[ℚ_[ℓ]] y)) =
      rationalEllAdicExternalCup ℓ f g d.val (n - d.val) n
        (Nat.add_sub_of_le (Nat.le_of_lt_succ d.isLt)) x y := by
  simp only [rationalEllAdicKunnethMap, DirectSum.toModule_lof,
    rationalEllAdicKunnethComponent_tmul]

/-- The actual Künneth map is determined by its projection-cup values
on the original direct-sum tensor generators. -/
theorem rationalEllAdicKunnethMap_unique (n : ℕ)
    (Φ : (⨁ d : Fin (n + 1),
      rationalEllAdicCohomology ℓ X d.val ⊗[ℚ_[ℓ]]
        rationalEllAdicCohomology ℓ Y (n - d.val)) →ₗ[ℚ_[ℓ]]
      rationalEllAdicCohomology ℓ (pullback f g) n)
    (hΦ : ∀ (d : Fin (n + 1)) (x : rationalEllAdicCohomology ℓ X d.val)
        (y : rationalEllAdicCohomology ℓ Y (n - d.val)),
      Φ (DirectSum.lof ℚ_[ℓ] (Fin (n + 1))
          (fun j => rationalEllAdicCohomology ℓ X j.val ⊗[ℚ_[ℓ]]
            rationalEllAdicCohomology ℓ Y (n - j.val)) d (x ⊗ₜ[ℚ_[ℓ]] y)) =
        rationalEllAdicExternalCup ℓ f g d.val (n - d.val) n
          (Nat.add_sub_of_le (Nat.le_of_lt_succ d.isLt)) x y) :
    Φ = rationalEllAdicKunnethMap ℓ f g n := by
  apply DirectSum.linearMap_ext
  intro d
  apply TensorProduct.ext'
  intro x y
  exact (hΦ d x y).trans (rationalEllAdicKunnethMap_lof_tmul ℓ f g n d x y).symm

end EtaleCohomology.Classical
