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

import Nyll.AlgebraicCurves.Models.Construction.Basic
import Nyll.AlgebraicCurves.Places.ValuationRings.RangeStalkEq
import Nyll.AlgebraicCurves.Models.LocalGeometry.EqRangeStalkEq
import Nyll.AlgebraicCurves.Models.LocalGeometry.ClosedPointRangeStalkEq
import Nyll.AlgebraicCurves.Models.Charts.IsAffineOpenMemFinsetField
import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
import Nyll.SchemeTheory.FunctionFields.ScalarFunctoriality

/-!
# The literal CurveModel of a given arithmetic smooth proper curve

No new curve is chosen: C and c remain definitionally unchanged and ffEquiv
is the identity. The general-field affine-neighborhood theorem is used.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicCurve

universe u

variable {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]
  (c : C ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]

/-- Package the given scheme itself, with its literal function field. -/
def literalCurveModel :
    letI : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
    CurveModel k C.functionField := by
  classical
  letI : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
  have hplace : ∀ x : closedPoints C, ∃ v : Place k C.functionField,
      (algebraMap (C.presheaf.stalk x.1) C.functionField).range =
        v.toValuationSubring.toSubring :=
    fun x => exists_place_range_stalk_eq c x.1 (mem_closedPoints_iff.mp x.2)
  choose pl hpl using hplace
  have hinj : Function.Injective pl := fun x y hxy =>
    Subtype.ext (eq_of_range_stalk_eq c x.1 y.1 (by rw [hpl x, hpl y, hxy]))
  have hsurj : Function.Surjective pl := fun v => by
    obtain ⟨x, hxc, hx⟩ := exists_closedPoint_range_stalk_eq c v
    refine ⟨⟨x, mem_closedPoints_iff.mpr hxc⟩, Place.ext ?_⟩
    apply ValuationSubring.toSubring_injective
    rw [← hpl, hx]
  exact
    { C := C
      toBase := c
      ffEquiv := RingEquiv.refl _
      ffEquiv_algebraMap := fun _ => rfl
      placeOfPoint := pl
      placeOfPoint_bijective := ⟨hinj, hsurj⟩
      range_stalk_eq := fun x => by
        rw [← hpl x]
        ext f
        exact ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩
      finset_subset_affineOpen := fun F =>
        exists_isAffineOpen_forall_mem_of_finset_of_field c F }

@[simp] theorem literalCurveModel_C :
    letI : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
    (literalCurveModel c).C = C := rfl

@[simp] theorem literalCurveModel_toBase :
    letI : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
    (literalCurveModel c).toBase = c := rfl

@[simp] theorem literalCurveModel_ffEquiv :
    letI : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
    (literalCurveModel c).ffEquiv = RingEquiv.refl C.functionField := rfl

/-- The open immersion keeps the exact function-field map used before
packaging the arithmetic compactification. No comparison isomorphism is chosen. -/
theorem literalCurveModel_functionFieldMap
    {U : Scheme.{u}} [IsIntegral U] (j : U ⟶ C) (hj : DenseRange j) :
    letI : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
    (j.functionFieldMap hj).comp (literalCurveModel c).ffEquiv.toRingHom =
      j.functionFieldMap hj := by
  rfl

/-- The germ comparison is literal, also before any geometric base change. -/
theorem literalCurveModel_germToFunctionField
    (U : C.Opens) [Nonempty (Scheme.Opens.toScheme U)] (t : Γ(C, U)) :
    letI : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
    (literalCurveModel c).ffEquiv.symm (C.germToFunctionField U t) =
      C.germToFunctionField U t := rfl

/-- The ancillary function-field instances used by the existing cover-model
owners. Perfectness is needed by the existing IsCurveOver supplier, but not
by literalCurveModel itself; in the number-field application it is automatic. -/
theorem literalCurveModel_functionField_properties [PerfectField k] :
    letI : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
    IsCurveOver k C.functionField ∧ Algebra.EssFiniteType k C.functionField := by
  let : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
  exact ⟨isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      c (RingEquiv.refl _) (fun _ => rfl),
    essFiniteType_functionField c⟩

end AlgebraicCurve
