/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CartierAdicCycleClass
public import Nyll.EtaleCohomology.Classical.DiagonalPointSectionIdeals
public import Nyll.EtaleCohomology.Classical.DiagonalPointSections
public import Nyll.EtaleCohomology.Classical.GraphAdicCycleClass
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalKunnethEdgeSplitting
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The actual diagonal with its two edge classes removed

Both original point-section restrictions of the original diagonal are
the original point class. Subtracting its two actual projection classes
therefore gives a class in the kernel of the original edge retraction.
This identifies the geometric class for the remaining middle comparison;
it does not assert that the middle Künneth map surjects onto that kernel.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open EtaleCohomology.Classical

namespace EtaleCohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (.of K)) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  [IsIntegral (pullback f f)]
  (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The two actual restrictions of the original diagonal recover the
original point class in each factor. -/
theorem rationalDiagonalCycleClass_edgeRetraction :
    rationalEllAdicEdgeRetraction K ℓ f f p hp p hp 2
        (rationalGraphCycleClass f f (𝟙 X) (Category.id_comp f) ℓ hℓ) =
      (rationalEffectiveCartierCycleClass f ℓ hℓ
        (sectionEffectiveCartierDivisor f p hp),
       rationalEffectiveCartierCycleClass f ℓ hℓ
        (sectionEffectiveCartierDivisor f p hp)) := by
  apply Prod.ext
  · exact rationalDiagonalCycleClass_kunnethSectionLeft f p hp ℓ hℓ
  · exact rationalDiagonalCycleClass_kunnethSectionRight f p hp ℓ hℓ

/-- The original geometric diagonal class after subtracting the two
actual edge projection classes of the chosen point. -/
def rationalDiagonalMiddleClass : rationalEllAdicCohomology ℓ (pullback f f) 2 :=
  rationalGraphCycleClass f f (𝟙 X) (Category.id_comp f) ℓ hℓ -
    rationalEllAdicEdgeMap ℓ f f 2
      (rationalEffectiveCartierCycleClass f ℓ hℓ
        (sectionEffectiveCartierDivisor f p hp),
       rationalEffectiveCartierCycleClass f ℓ hℓ
        (sectionEffectiveCartierDivisor f p hp))

/-- The normalized actual diagonal has zero original edge retraction. -/
theorem rationalDiagonalMiddleClass_edgeRetraction :
    rationalEllAdicEdgeRetraction K ℓ f f p hp p hp 2
      (rationalDiagonalMiddleClass f p hp ℓ hℓ) = 0 := by
  rw [rationalDiagonalMiddleClass, map_sub,
    rationalDiagonalCycleClass_edgeRetraction f p hp ℓ hℓ,
    rationalEllAdicEdgeRetraction_apply_edgeMap K ℓ f f p hp p hp 1, sub_self]

/-- The genuine normalized diagonal belongs to the actual kernel
which contains every actual middle Künneth class. -/
theorem rationalDiagonalMiddleClass_mem_ker :
    rationalDiagonalMiddleClass f p hp ℓ hℓ ∈
      LinearMap.ker (rationalEllAdicEdgeRetraction K ℓ f f p hp p hp 2) :=
  rationalDiagonalMiddleClass_edgeRetraction f p hp ℓ hℓ

/-- The original diagonal is the sum of its original two geometric
edge classes and the actual normalized diagonal. -/
theorem rationalDiagonalCycleClass_eq_edges_add_middle :
    rationalGraphCycleClass f f (𝟙 X) (Category.id_comp f) ℓ hℓ =
      rationalEllAdicEdgeMap ℓ f f 2
        (rationalEffectiveCartierCycleClass f ℓ hℓ
          (sectionEffectiveCartierDivisor f p hp),
         rationalEffectiveCartierCycleClass f ℓ hℓ
          (sectionEffectiveCartierDivisor f p hp)) +
      rationalDiagonalMiddleClass f p hp ℓ hℓ := by
  let d := rationalGraphCycleClass f f (𝟙 X) (Category.id_comp f) ℓ hℓ
  let a := rationalEllAdicEdgeMap ℓ f f 2
    (rationalEffectiveCartierCycleClass f ℓ hℓ (sectionEffectiveCartierDivisor f p hp),
     rationalEffectiveCartierCycleClass f ℓ hℓ (sectionEffectiveCartierDivisor f p hp))
  change d = a + (d - a)
  exact (sub_add_cancel d a).symm.trans (add_comm (d - a) a)

end EtaleCohomology
