/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralAlgClosed
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Actual products of integral smooth schemes over an algebraically closed field

Geometric integrality of the original smooth factor, its flatness and
openness, and the actual local Noetherian property of the other factor
supply integrality of their original scheme-theoretic product.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The original product is integral. Every hypothesis needed by the
geometrically integral pullback theorem comes from the displayed factors. -/
theorem isIntegral_pullback_of_smooth_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    [Smooth f] [LocallyOfFiniteType g] : IsIntegral (pullback f g) := by
  have : GeometricallyIntegral f := geometricallyIntegral_of_isAlgClosed f
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  infer_instance

end AlgebraicGeometry
