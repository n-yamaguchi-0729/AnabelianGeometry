/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.FunctionFields.CurveGenericUnitsVanishing
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitGlobal
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorH1
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Vanishing of native H²(Gm) on a smooth proper curve

The actual global divisor comparison identifies the generic-unit quotient
with the original closed-point divisor sheaf. Its first cohomology vanishes
over an algebraically closed field. The original generic-unit long exact
sequence and the proved Tsen vanishing then annihilate native H²(Gm).
Every comparison and vanishing statement is supplied by the curve itself.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open EtaleCohomology

namespace AlgebraicCurve

/-- The original generic-unit quotient has zero first cohomology on a
smooth proper integral curve over an algebraically closed field. -/
theorem smoothProperCurve_genericUnitQuotient_H1_eq_zero
    (K : Type u) [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 c] [IsProper c]
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient X) 1) : a = 0 := by
  let e := ((Sheaf.functorH X.smallEtaleTopology 1).mapIso
    (smoothCurveClosedPointDivisorGenericUnitIso c)).addCommGroupIsoToAddEquiv
  obtain ⟨b, hb⟩ := e.surjective a
  exact hb.symm.trans
    ((congrArg e (closedPointDivisorSheaf_H1_eq_zero_of_proper c b)).trans e.map_zero)

/-- Native étale H² of the original multiplicative-group sheaf vanishes
on a smooth proper integral curve over an algebraically closed field. -/
theorem smoothProperCurve_multiplicativeGroup_H2_eq_zero
    (K : Type u) [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 c] [IsProper c]
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 2) : a = 0 := by
  obtain ⟨b, hb⟩ := Sheaf.H.longSequence_exact₁
    (etaleGenericUnitShortComplex_shortExact X) a
    (smoothCurve_genericPoint_units_H2_eq_zero K c _) (n₀ := 1) rfl
  have hbzero : b = 0 := smoothProperCurve_genericUnitQuotient_H1_eq_zero K c b
  exact hb.symm.trans
    ((congrArg (Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 1 2 rfl) hbzero).trans
      (map_zero _))

end AlgebraicCurve
