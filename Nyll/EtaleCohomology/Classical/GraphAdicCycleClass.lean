/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.CartierAdicCycleClass
public import Nyll.EtaleCohomology.Classical.GraphCartierCycleClass
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Original ℓ-adic graph and diagonal classes

The actual graph Cartier divisor in the original scheme product supplies
compatible finite cycle classes and hence original integral and rational
ℓ-adic classes. Identity graphs give the diagonal classes in the same groups.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open EtaleCohomology.Classical

namespace EtaleCohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
  [SmoothOfRelativeDimension 1 f] (g : Y ⟶ Spec (.of K))
  [IsIntegral (pullback f g)] (a : Y ⟶ X) (ha : a ≫ f = g)
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The actual graph class in original finite cyclic étale cohomology. -/
def finiteGraphCycleClass (n : ℕ) : finiteLevelCohomology (pullback f g) ℓ n 2 :=
  finiteEffectiveCartierCycleClass (pullback.snd f g ≫ g) ℓ hℓ n
    (graphEffectiveCartierDivisor f g a ha)

/-- The graph's finite classes satisfy the original coefficient reductions. -/
theorem finiteGraphCycleClass_reduction (n : ℕ) :
    finiteLevelReduction (pullback f g) ℓ n 2
        (finiteGraphCycleClass f g a ha ℓ hℓ (n + 1)) =
      finiteGraphCycleClass f g a ha ℓ hℓ n :=
  finiteEffectiveCartierCycleClass_reduction (pullback.snd f g ≫ g) ℓ hℓ n
    (graphEffectiveCartierDivisor f g a ha)

/-- The graph class in the original integral inverse limit. -/
def integralGraphCycleClass : ellAdicCohomology (pullback f g) ℓ 2 :=
  integralEffectiveCartierCycleClass (pullback.snd f g ≫ g) ℓ hℓ
    (graphEffectiveCartierDivisor f g a ha)

/-- Every integral projection is the original graph class at that level. -/
theorem integralGraphCycleClass_projection (n : ℕ) :
    ellAdicProjection (pullback f g) ℓ 2 n
        (integralGraphCycleClass f g a ha ℓ hℓ) =
      finiteGraphCycleClass f g a ha ℓ hℓ n := rfl

/-- The graph class in original rational ℓ-adic cohomology. -/
def rationalGraphCycleClass : rationalEllAdicCohomology ℓ (pullback f g) 2 :=
  rationalEffectiveCartierCycleClass (pullback.snd f g ≫ g) ℓ hℓ
    (graphEffectiveCartierDivisor f g a ha)

end EtaleCohomology
