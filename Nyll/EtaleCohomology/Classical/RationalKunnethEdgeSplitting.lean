/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalAdicCup
public import Nyll.EtaleCohomology.Classical.RationalKunnethMap
public import Nyll.EtaleCohomology.Classical.RationalKunnethSections
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Splitting the two original product-cohomology edge images

The sum of the two original projection pullbacks is injective in every
positive degree over a separably closed field when the factors have
actual rational points. Its explicit left inverse is pullback along the
two actual point sections. The actual middle Künneth component in degree
two is killed by this left inverse. This separates the two edge images
from the middle image without asserting that the middle map is injective
or that the full Künneth map is surjective.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

namespace EtaleCohomology.Classical

section EdgeMap

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The sum of the actual two projection pullbacks on the original
rational cohomology of the actual fibre product. -/
def rationalEllAdicEdgeMap (i : ℕ) :
    (rationalEllAdicCohomology ℓ X i × rationalEllAdicCohomology ℓ Y i) →ₗ[ℚ_[ℓ]]
      rationalEllAdicCohomology ℓ (pullback f g) i :=
  (rationalEllAdicCohomologyPullback ℓ (pullback.fst f g) i).coprod
    (rationalEllAdicCohomologyPullback ℓ (pullback.snd f g) i)

/-- The two edge classes are the actual external cups with the
original units on the opposite factors. -/
theorem rationalEllAdicEdgeMap_eq_externalCup (i : ℕ)
    (x : rationalEllAdicCohomology ℓ X i) (y : rationalEllAdicCohomology ℓ Y i) :
    rationalEllAdicEdgeMap ℓ f g i (x, y) =
      rationalEllAdicExternalCup ℓ f g i 0 i (add_zero i) x (rationalEllAdicCupUnit Y ℓ) +
        rationalEllAdicExternalCup ℓ f g 0 i i (zero_add i) (rationalEllAdicCupUnit X ℓ) y := by
  exact (congrArg₂ (· + ·)
    (rationalEllAdicExternalCup_unit_right ℓ f g i x)
    (rationalEllAdicExternalCup_unit_left ℓ f g i y)).symm

end EdgeMap

section PointRetraction

variable (K : Type u) [Field K] [IsSepClosed K] (ℓ : ℕ) [Fact ℓ.Prime]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
  (g : Y ⟶ Spec (CommRingCat.of K))
  (pX : Spec (CommRingCat.of K) ⟶ X) (hpX : pX ≫ f = 𝟙 _)
  (pY : Spec (CommRingCat.of K) ⟶ Y) (hpY : pY ≫ g = 𝟙 _)

/-- Pullback along the two actual point sections, with values in
the original two cohomology groups. -/
def rationalEllAdicEdgeRetraction (i : ℕ) :
    rationalEllAdicCohomology ℓ (pullback f g) i →ₗ[ℚ_[ℓ]]
      (rationalEllAdicCohomology ℓ X i × rationalEllAdicCohomology ℓ Y i) :=
  (rationalEllAdicCohomologyPullback ℓ (kunnethSectionLeft f g pY hpY) i).prod
    (rationalEllAdicCohomologyPullback ℓ (kunnethSectionRight f g pX hpX) i)

/-- In positive degree the original point sections recover both
classes from the sum of the two actual projection pullbacks. -/
theorem rationalEllAdicEdgeRetraction_apply_edgeMap (i : ℕ)
    (x : rationalEllAdicCohomology ℓ X (i + 1))
    (y : rationalEllAdicCohomology ℓ Y (i + 1)) :
    rationalEllAdicEdgeRetraction K ℓ f g pX hpX pY hpY (i + 1)
        (rationalEllAdicEdgeMap ℓ f g (i + 1) (x, y)) = (x, y) := by
  let L := rationalEllAdicCohomologyPullback ℓ (kunnethSectionLeft f g pY hpY) (i + 1)
  let R := rationalEllAdicCohomologyPullback ℓ (kunnethSectionRight f g pX hpX) (i + 1)
  let A := rationalEllAdicCohomologyPullback ℓ (pullback.fst f g) (i + 1)
  let B := rationalEllAdicCohomologyPullback ℓ (pullback.snd f g) (i + 1)
  have hLA : L (A x) = x := LinearMap.congr_fun
    (rationalEllAdicPullback_kunnethSectionLeft_fst f g ℓ pY hpY (i + 1)) x
  have hLB : L (B y) = 0 := LinearMap.congr_fun
    (rationalEllAdicPullback_kunnethSectionLeft_snd K ℓ f g pY hpY i) y
  have hRA : R (A x) = 0 := LinearMap.congr_fun
    (rationalEllAdicPullback_kunnethSectionRight_fst K ℓ f g pX hpX i) x
  have hRB : R (B y) = y := LinearMap.congr_fun
    (rationalEllAdicPullback_kunnethSectionRight_snd f g ℓ pX hpX (i + 1)) y
  apply Prod.ext
  · change L (A x + B y) = x
    rw [map_add, hLA, hLB, add_zero]
  · change R (A x + B y) = y
    rw [map_add, hRA, hRB, zero_add]

/-- The two actual point-section pullbacks form an explicit left
inverse to the original edge map in every positive degree. -/
theorem rationalEllAdicEdgeRetraction_leftInverse (i : ℕ) :
    Function.LeftInverse (rationalEllAdicEdgeRetraction K ℓ f g pX hpX pY hpY (i + 1))
      (rationalEllAdicEdgeMap ℓ f g (i + 1)) := by
  intro z
  exact rationalEllAdicEdgeRetraction_apply_edgeMap K ℓ f g pX hpX pY hpY i z.1 z.2

include pX hpX pY hpY in
/-- The sum of the original projection pullbacks is injective in
positive degree; the point-section calculation supplies its left inverse. -/
theorem rationalEllAdicEdgeMap_injective (i : ℕ) :
    Function.Injective (rationalEllAdicEdgeMap ℓ f g (i + 1)) :=
  (rationalEllAdicEdgeRetraction_leftInverse K ℓ f g pX hpX pY hpY i).injective

/-- The actual middle Künneth component is killed by both original
point-section pullbacks. -/
theorem rationalEllAdicEdgeRetraction_comp_middle :
    (rationalEllAdicEdgeRetraction K ℓ f g pX hpX pY hpY 2).comp
        (rationalEllAdicKunnethComponent ℓ f g 1 1 2 rfl) = 0 := by
  apply TensorProduct.ext'
  intro x y
  apply Prod.ext
  · change rationalEllAdicCohomologyPullback ℓ (kunnethSectionLeft f g pY hpY) 2
      (rationalEllAdicExternalCup ℓ f g 1 1 2 rfl x y) = 0
    exact rationalEllAdicExternalCup_kunnethSectionLeft_eq_zero K ℓ f g pY hpY 1 0 2 rfl x y
  · change rationalEllAdicCohomologyPullback ℓ (kunnethSectionRight f g pX hpX) 2
      (rationalEllAdicExternalCup ℓ f g 1 1 2 rfl x y) = 0
    exact rationalEllAdicExternalCup_kunnethSectionRight_eq_zero K ℓ f g pX hpX 0 1 2 rfl x y

/-- Every original middle Künneth class lies in the kernel of the
actual edge retraction. -/
theorem rationalEllAdicKunnethMiddle_range_le_ker_edgeRetraction :
    LinearMap.range (rationalEllAdicKunnethComponent ℓ f g 1 1 2 rfl) ≤
      LinearMap.ker (rationalEllAdicEdgeRetraction K ℓ f g pX hpX pY hpY 2) := by
  intro z hz
  obtain ⟨a, rfl⟩ := hz
  exact LinearMap.congr_fun
    (rationalEllAdicEdgeRetraction_comp_middle K ℓ f g pX hpX pY hpY) a

end PointRetraction

end EtaleCohomology.Classical
