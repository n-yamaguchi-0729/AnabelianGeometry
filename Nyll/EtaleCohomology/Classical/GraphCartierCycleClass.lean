/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.HomInvertibleKerCompEqId
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.EffectiveCartierIdeal
public import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivOfPoint
public import Nyll.EtaleCohomology.Classical.CartierCycleClass
public import Nyll.SchemeTheory.Divisors.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Actual graph and diagonal cycle classes on products with smooth curves

The original graph is a section of the smooth relative curve projection.
Its actual kernel ideal is invertible by the section theorem, and its actual
local equations therefore make it an effective Cartier divisor. Applying
the original generic-unit and Kummer boundaries gives its original étale
H² class on the original scheme-theoretic product.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

/-- The actual graph kernel as an actual effective Cartier divisor in a
product with a separated smooth relative curve. -/
def graphEffectiveCartierDivisor
    {X Y S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] (g : Y ⟶ S)
    (a : Y ⟶ X) (ha : a ≫ f = g) :
    Scheme.EffectiveCartierDivisor (pullback f g) := by
  have : MorphismProperty.IsStableUnderBaseChange
      (C := Scheme.{u}) (fun {_ _} h => SmoothOfRelativeDimension 1 h) :=
    smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  have : SmoothOfRelativeDimension 1 (pullback.snd f g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {_ _ : Scheme.{u}} h => SmoothOfRelativeDimension 1 h)
      (IsPullback.of_hasPullback f g) inferInstance
  exact ⟨(graphOver f a ha).ker,
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id
      (graphOver f a ha) (graphOver_snd f a ha)).isEffectiveCartier⟩

/-- The divisor used in the cycle construction is the kernel of the
original graph morphism. -/
theorem graphEffectiveCartierDivisor_ideal
    {X Y S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] (g : Y ⟶ S)
    (a : Y ⟶ X) (ha : a ≫ f = g) :
    (graphEffectiveCartierDivisor f g a ha).1 = (graphOver f a ha).ker := rfl

/-- The graph cycle class in the original product's actual étale H² of
roots of unity. The diagonal is obtained by taking `a = 𝟙 X` and `g = f`. -/
def graphCartierCycleClass
    {X Y S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] (g : Y ⟶ S)
    [IsIntegral (pullback f g)] (a : Y ⟶ X) (ha : a ≫ f = g)
    {n : ℕ} (hn : 0 < n) (hnP : IsUnit (n : Γ(pullback f g, ⊤))) :
    Sheaf.H.{u} (etaleRootsOfUnitySheaf (pullback f g) n) 2 :=
  effectiveCartierCycleClass (graphEffectiveCartierDivisor f g a ha) hn hnP

end EtaleCohomology
