/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
public import Nyll.SchemeTheory.FunctionFields.ScalarFunctoriality

/-!
# The literal CurveModel of a given arithmetic smooth proper curve

No new curve is chosen: C and c remain definitionally unchanged and ffEquiv
is the identity. The general-field affine-neighborhood theorem is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicCurve

universe u

variable {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]
  (c : C ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]

/-- Package the given scheme itself, with its literal function field. -/
def literalCurveModel :
    let _ : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
    CurveModel k C.functionField :=
  CurveModel.ofSmoothProperCurve c

@[simp] theorem literalCurveModel_C :
    let _ : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
    (literalCurveModel c).C = C := rfl

@[simp] theorem literalCurveModel_toBase :
    let _ : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
    (literalCurveModel c).toBase = c := rfl

@[simp] theorem literalCurveModel_ffEquiv :
    let _ : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
    (literalCurveModel c).ffEquiv = RingEquiv.refl C.functionField := rfl

/-- The open immersion keeps the exact function-field map used before
packaging the arithmetic compactification. No comparison isomorphism is chosen. -/
theorem literalCurveModel_functionFieldMap
    {U : Scheme.{u}} [IsIntegral U] (j : U ⟶ C) (hj : DenseRange j) :
    let _ : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
    (j.functionFieldMap hj).comp (literalCurveModel c).ffEquiv.toRingHom =
      j.functionFieldMap hj := by
  rfl

/-- The germ comparison is literal, also before any geometric base change. -/
theorem literalCurveModel_germToFunctionField
    (U : C.Opens) [Nonempty (Scheme.Opens.toScheme U)] (t : Γ(C, U)) :
    let _ : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
    (literalCurveModel c).ffEquiv.symm (C.germToFunctionField U t) =
      C.germToFunctionField U t := rfl

/-- The ancillary function-field instances used by the existing cover-model
owners. Perfectness is needed by the existing IsCurveOver supplier, but not
by literalCurveModel itself; in the number-field application it is automatic. -/
theorem literalCurveModel_functionField_properties [PerfectField k] :
    let _ : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
    IsCurveOver k C.functionField ∧ Algebra.EssFiniteType k C.functionField := by
  intro algKF
  exact ⟨isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      c (RingEquiv.refl _) (fun _ => rfl),
    essFiniteType_functionField c⟩

end AlgebraicCurve
