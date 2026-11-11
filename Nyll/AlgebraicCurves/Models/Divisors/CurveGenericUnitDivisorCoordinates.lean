/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Divisors.CurveDivisorCohomologySections
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitGlobal
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Original generic-unit quotient H⁰ in divisor coordinates

The actual global divisor-sheaf isomorphism and the original place
correspondence of a curve model identify H⁰ of the generic-unit quotient
with its divisor group. This keeps the native sheaf cohomology maps; the
principal-divisor calculation is supplied separately from local orders.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory
open EtaleCohomology

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F)

/-- Native H⁰ of the original generic-unit quotient, expressed in the
original divisor group through the proved global divisor comparison. -/
def genericUnitDivisorH0Equiv :
    Sheaf.H.{u} (etaleGenericUnitQuotient M.C) 0 ≃+ Divisor K F :=
  (CategoryTheory.Iso.addCommGroupIsoToAddEquiv
    ((Sheaf.functorH M.C.smallEtaleTopology 0).mapIso
      (smoothCurveClosedPointDivisorGenericUnitIso M.toBase).symm)).trans
    M.divisorSheafH0Equiv

/-- The divisor coordinates are obtained by the original H⁰ map of the
inverse global sheaf isomorphism. -/
theorem genericUnitDivisorH0Equiv_apply
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient M.C) 0) :
    M.genericUnitDivisorH0Equiv a = M.divisorSheafH0Equiv
      (Sheaf.H.map (smoothCurveClosedPointDivisorGenericUnitIso M.toBase).inv 0 a) := rfl

/-- The original map from generic units, followed by actual divisor
coordinates, is an additive map to the model's divisor group. -/
def genericUnitsDivisorH0Map :
    Sheaf.H.{u}
      ((etaleAbelianPushforward (M.C.fromSpecStalk (genericPoint M.C))).obj
        (etaleMultiplicativeGroupSheaf (Spec (.of M.C.functionField)))) 0 →+
      Divisor K F :=
  M.genericUnitDivisorH0Equiv.toAddMonoidHom.comp
    (Sheaf.H.map (etaleGenericUnitShortComplex M.C).g 0)

end AlgebraicCurve.CurveModel
