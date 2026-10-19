/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_exists_hom_of_algHom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

The shared structural-map proof is extracted from the NYLL adaptation of
that file and maintained in SchemeTheory.FunctionFields.StructureMorphism.
The open-chart point constructions and
their point-compatibility proofs are local additions.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/
import Nyll.AlgebraicCurves.Models.Construction.Basic
import Nyll.SchemeTheory.FunctionFields.OpenChartGenericPoints
import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-! # Generic chart points of curve models over the ground field -/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace AlgebraicCurve
universe u

namespace CurveModel

/-- The canonical model coordinate gives a generic point over the ground field. -/
theorem functionFieldChartPoint_comp_toBase
    {K F : Type u} [Field K] [Field F] [Algebra K F] (M : CurveModel K F) :
    M.C.functionFieldChartPoint M.ffEquiv ≫ M.toBase =
      Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
  have hcoeff : M.ffEquiv.symm.toRingHom.comp (baseToFunctionField M.toBase) =
      algebraMap K F := by
    ext a
    change M.ffEquiv.symm (baseToFunctionField M.toBase a) = _
    rw [← M.ffEquiv_algebraMap, M.ffEquiv.symm_apply_apply]
  unfold Scheme.functionFieldChartPoint
  rw [Category.assoc, fromSpecStalk_genericPoint_comp_base,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcoeff]

/-- The generic point of the actual arithmetic open satisfies the exact
arithmetic base-point equation after extension to the ambient field. -/
theorem functionFieldChartPoint_open_ambient_comp_toBase
    {K F Ω : Type u} [Field K] [Field F] [Field Ω]
    [Algebra K F] [Algebra F Ω] [Algebra K Ω] [IsScalarTower K F Ω]
    (M : CurveModel K F) {X : Scheme.{u}} [IsIntegral X]
    (i : X ⟶ M.C) [IsOpenImmersion i] :
    (Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫
        X.functionFieldChartPoint (M.ffEquiv.trans i.functionFieldRingEquivOfIsOpenImmersion)) ≫
      (i ≫ M.toBase) = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [Category.assoc, ← Category.assoc
      (X.functionFieldChartPoint (M.ffEquiv.trans i.functionFieldRingEquivOfIsOpenImmersion))
      i M.toBase,
    Scheme.functionFieldChartPoint_comp_openImmersion,
    functionFieldChartPoint_comp_toBase,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq K F Ω]

end CurveModel
end AlgebraicCurve
