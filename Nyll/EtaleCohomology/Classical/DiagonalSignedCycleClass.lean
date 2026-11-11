/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CartierAdicCycleClass
public import Nyll.EtaleCohomology.Classical.CartierAdicCyclePullback
public import Nyll.EtaleCohomology.Classical.CartierAdicLineBundleComparison
public import Nyll.EtaleCohomology.Classical.DiagonalDivisorBundle
public import Nyll.EtaleCohomology.Classical.DiagonalMiddleClass
public import Nyll.EtaleCohomology.Classical.DiagonalPointSectionIdeals
public import Nyll.EtaleCohomology.Classical.GraphAdicCycleClass
public import Nyll.EtaleCohomology.Classical.GraphCartierCycleClass
public import Nyll.EtaleCohomology.Classical.RationalKunnethEdgeSplitting
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The original normalized diagonal as an actual signed Cartier class

The original point pullbacks have exactly the original projection
classes. Their actual product ideal therefore represents the sum of
the two edges. Consequently the previously constructed normalized
diagonal is the original cycle class of the explicit divisor difference
whose actual line bundle is compared with the Abel–Jacobi family.
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

/-- The actual first point divisor has the original first projection
class, expressed over the common product structure morphism. -/
theorem productPointFstEffectiveCartierDivisor_rationalCycleClass :
    rationalEffectiveCartierCycleClass (pullback.snd f f ≫ f) ℓ hℓ
        (productPointFstEffectiveCartierDivisor f p hp) =
      rationalEllAdicCohomologyPullback ℓ (pullback.fst f f) 2
        (rationalEffectiveCartierCycleClass f ℓ hℓ
          (sectionEffectiveCartierDivisor f p hp)) := by
  have h := rationalEffectiveCartierCycleClass_pullback (pullback.fst f f) f ℓ hℓ
    (sectionEffectiveCartierDivisor f p hp)
    (productPointFstEffectiveCartierDivisor f p hp).2
  rw [pullback.condition] at h
  exact h.symm

/-- The actual second point divisor has the original second
projection class on the same original product. -/
theorem productPointSndEffectiveCartierDivisor_rationalCycleClass :
    rationalEffectiveCartierCycleClass (pullback.snd f f ≫ f) ℓ hℓ
        (productPointSndEffectiveCartierDivisor f p hp) =
      rationalEllAdicCohomologyPullback ℓ (pullback.snd f f) 2
        (rationalEffectiveCartierCycleClass f ℓ hℓ
          (sectionEffectiveCartierDivisor f p hp)) :=
  (rationalEffectiveCartierCycleClass_pullback (pullback.snd f f) f ℓ hℓ
    (sectionEffectiveCartierDivisor f p hp)
    (productPointSndEffectiveCartierDivisor f p hp).2).symm

/-- The full actual edge divisor represents the two original edge
classes, by actual Cartier addition and actual pullback. -/
theorem diagonalEdgeEffectiveCartierDivisor_rationalCycleClass :
    rationalEffectiveCartierCycleClass (pullback.snd f f ≫ f) ℓ hℓ
        (diagonalEdgeEffectiveCartierDivisor f p hp) =
      rationalEllAdicEdgeMap ℓ f f 2
        (rationalEffectiveCartierCycleClass f ℓ hℓ
          (sectionEffectiveCartierDivisor f p hp),
         rationalEffectiveCartierCycleClass f ℓ hℓ
          (sectionEffectiveCartierDivisor f p hp)) := by
  change rationalEffectiveCartierCycleClass (pullback.snd f f ≫ f) ℓ hℓ
    ⟨(productPointFstEffectiveCartierDivisor f p hp).1 *
      (productPointSndEffectiveCartierDivisor f p hp).1, _⟩ =
    rationalEllAdicCohomologyPullback ℓ (pullback.fst f f) 2
      (rationalEffectiveCartierCycleClass f ℓ hℓ (sectionEffectiveCartierDivisor f p hp)) +
    rationalEllAdicCohomologyPullback ℓ (pullback.snd f f) 2
      (rationalEffectiveCartierCycleClass f ℓ hℓ (sectionEffectiveCartierDivisor f p hp))
  rw [rationalEffectiveCartierCycleClass_mul,
    productPointFstEffectiveCartierDivisor_rationalCycleClass,
    productPointSndEffectiveCartierDivisor_rationalCycleClass]

/-- The actual normalized diagonal is the original signed cycle
class of the explicit diagonal-minus-two-point-divisors bundle. -/
theorem rationalDiagonalMiddleClass_eq_signedCycleClass :
    rationalDiagonalMiddleClass f p hp ℓ hℓ =
      rationalEffectiveCartierCycleClass (pullback.snd f f ≫ f) ℓ hℓ
          (graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)) -
        rationalEffectiveCartierCycleClass (pullback.snd f f ≫ f) ℓ hℓ
          (diagonalEdgeEffectiveCartierDivisor f p hp) := by
  rw [rationalDiagonalMiddleClass, rationalGraphCycleClass,
    diagonalEdgeEffectiveCartierDivisor_rationalCycleClass]

end EtaleCohomology
