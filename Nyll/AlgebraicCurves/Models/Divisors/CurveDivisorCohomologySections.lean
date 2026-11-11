/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGlobalSections
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Data.Finsupp.Basic

/-!
# Curve-model coordinates on the actual divisor and generic-unit H⁰

The original place equivalence and function-field equivalence provide the
coordinates used in the Picard comparison. The divisor coordinates retain
the actual coproduct projection at each original closed point.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleCohomology

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F)

/-- Actual H⁰ of the closed-point divisor sheaf is the original divisor
group of the model's function field. -/
def divisorSheafH0Equiv :
    Sheaf.H.{u} (closedPointDivisorSheaf M.C) 0 ≃+ Divisor K F := by
  have : CompactSpace M.C := QuasiCompact.compactSpace_of_compactSpace M.toBase
  exact (closedPointDivisorH0FinsuppAddEquiv M.C).trans (Finsupp.domCongr M.placeEquiv)

/-- The coefficient at an original place is the original sheaf component
projection at its corresponding closed point. -/
theorem divisorSheafH0Equiv_apply
    (a : Sheaf.H.{u} (closedPointDivisorSheaf M.C) 0) (w : Place K F) :
    M.divisorSheafH0Equiv a w =
      closedPointDivisorGlobalCoefficient M.C (M.placeEquiv.symm w)
        (Sheaf.H.equiv₀.{u} (closedPointDivisorSheaf M.C)
          (MorphismProperty.Over.mkIdTerminal
            (show MorphismProperty Scheme.{u} from @Etale) M.C) a) := by
  have : CompactSpace M.C := QuasiCompact.compactSpace_of_compactSpace M.toBase
  change Finsupp.equivMapDomain M.placeEquiv
    (closedPointDivisorH0FinsuppAddEquiv M.C a) w = _
  rw [Finsupp.equivMapDomain_apply]
  exact closedPointDivisorSectionsFinsuppAddEquiv_apply M.C
    (Sheaf.H.equiv₀.{u} (closedPointDivisorSheaf M.C)
      (MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) M.C) a)
    (M.placeEquiv.symm w)

/-- Actual H⁰ of generic-point units, expressed in the original field
specified by the curve model. -/
def genericUnitsH0FieldEquiv :
    Sheaf.H.{u}
      ((etaleAbelianPushforward (M.C.fromSpecStalk (genericPoint M.C))).obj
        (etaleMultiplicativeGroupSheaf (Spec (.of M.C.functionField)))) 0 ≃+
      Additive Fˣ :=
  (genericPointUnitsH0Equiv M.C).trans
    (Units.mapEquiv M.ffEquiv.symm.toMulEquiv).toAdditive

end AlgebraicCurve.CurveModel
