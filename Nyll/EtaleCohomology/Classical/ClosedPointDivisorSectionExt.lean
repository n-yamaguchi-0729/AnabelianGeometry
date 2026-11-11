/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Coefficient extensionality for original divisor sections

On a quasi-compact source, the proved finite-support formula recovers a
section from its original coproduct projections. Consequently the original
integer values on closed-point residue fibers determine the section.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

namespace EtaleCohomology

/-- The original residue-fiber coefficients determine a divisor-sheaf
section on a quasi-compact étale source. -/
theorem closedPointDivisorSection_ext_of_quasiCompact
    (X : Scheme.{u}) (V : X.Etale) [QuasiCompact (terminal.from V.left)]
    (s t : (closedPointDivisorSheaf X).obj.obj (op V))
    (h : ∀ (x : closedPoints X) (z : closedPointResidueFiber X x V),
      closedPointDivisorSummandSectionsAddEquiv X x V
        ((closedPointDivisorSheafComponentProjection X x).hom.app (op V) s) z =
      closedPointDivisorSummandSectionsAddEquiv X x V
        ((closedPointDivisorSheafComponentProjection X x).hom.app (op V) t) z) :
    s = t := by
  classical
  have hp (x : closedPoints X) :
      (closedPointDivisorSheafComponentProjection X x).hom.app (op V) (s - t) = 0 := by
    rw [map_sub]
    apply sub_eq_zero.mpr
    apply (closedPointDivisorSummandSectionsAddEquiv X x V).injective
    funext z
    exact h x z
  have hShape : HasColimitsOfShape (Discrete (closedPoints X))
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape X
  obtain ⟨A, hA⟩ := closedPointDivisorSheaf_finiteSupport_of_quasiCompact X V (s - t)
  change s - t = ∑ x ∈ A,
    (closedPointDivisorSheafInjection X x).hom.app (op V)
      ((closedPointDivisorSheafComponentProjection X x).hom.app (op V) (s - t)) at hA
  apply sub_eq_zero.mp
  rw [hA]
  apply Finset.sum_eq_zero
  intro x hx
  rw [hp, map_zero]

end EtaleCohomology
