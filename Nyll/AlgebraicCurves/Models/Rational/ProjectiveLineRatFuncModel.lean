/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_CurveModelConstruction.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/
module

public import Nyll.SchemeTheory.ProjectiveSpace.ProjectiveLineRatFuncCoordinate
public import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
public import Nyll.AlgebraicCurves.Models.FunctionFields.FieldReparametrization
public import Nyll.SchemeTheory.ProjectiveSpace.ProjectiveLineSmooth

/-! # The literal projective-line CurveModel of the rational-function field -/
@[expose] public section

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace
namespace AlgebraicGeometry.ProjSpace
attribute [local instance] MvPolynomial.gradedAlgebra projectiveSpace_isIntegral
  projectiveLine_smoothOfRelativeDimension
variable (k : Type u) [Field k]

/-- A rational CurveModel whose curve and structural morphism are literally
the given projective-space construction. -/
def projectiveLineRatFuncModel : CurveModel k (RatFunc k) := by
  let : Algebra k
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k) : Scheme).functionField :=
    (baseToFunctionField (π k 1)).toAlgebra
  exact CurveModel.reparametrizeField (projectiveLineRatFuncAlgEquiv k).symm
    (literalCurveModel (π k 1))

@[simp] theorem projectiveLineRatFuncModel_C :
    (projectiveLineRatFuncModel k).C =
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k) : Scheme) := rfl

@[simp] theorem projectiveLineRatFuncModel_toBase :
    (projectiveLineRatFuncModel k).toBase = π k 1 := rfl

@[simp] theorem projectiveLineRatFuncModel_ffEquiv :
    (projectiveLineRatFuncModel k).ffEquiv = projectiveLineRatFuncEquiv k := rfl

end AlgebraicGeometry.ProjSpace
