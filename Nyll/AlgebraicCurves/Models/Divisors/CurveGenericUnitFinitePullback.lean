/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.Maps.Maps
public import Nyll.AlgebraicCurves.Divisors.Correspondences.Correspondences
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Divisors.CurveDivisorCohomologySections
public import Nyll.AlgebraicCurves.Models.Divisors.CurveFiniteEtaleModel
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitDivisorCoordinates
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorFiniteCoefficients
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteRestriction
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
public import Nyll.SchemeTheory.FunctionFields.ScalarFunctoriality
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Native generic-unit divisor pullback through an actual finite cover

The coefficient of the original native H⁰ pullback is read at the actual
image point. The canonical field embedding restricts its place to that
same point, and étaleness makes its ramification index one. Consequently
the original H⁰ coordinates are exactly divisor pullback, with the actual
function-field degree as their degree multiplier.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups EtaleCohomology

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) [IsNormalIntegral M.C]
  (Y : FiniteEtale M.C) [IsConnected Y]

/-- The original quotient H⁰ pullback is the divisor pullback along
the canonical field map of the original connected finite étale cover. -/
theorem genericUnitDivisorH0Equiv_finitePullback :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let _ : Algebra K Y.left.functionField :=
      (baseToFunctionField ((show Y.left ⟶ M.C from Y.hom) ≫ M.toBase)).toAlgebra
    let φ := M.finiteEtaleModelFieldMap Y
    let _ : Algebra F Y.left.functionField := algebraAlong φ
    let _ : IsScalarTower K F Y.left.functionField := isScalarTower_along φ
    let _ : FiniteDimensional F Y.left.functionField :=
      (M.finiteEtaleModelFieldMap_properties Y).1
    let _ : Algebra.IsIntegral F Y.left.functionField := Algebra.IsIntegral.of_finite F _
    let _ : HasPrincipalDivisors K Y.left.functionField :=
      (isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
        (M.finiteEtaleModel Y).toBase (M.finiteEtaleModel Y).ffEquiv
          (M.finiteEtaleModel Y).ffEquiv_algebraMap).toHasPrincipalDivisors
    ∀ a : Sheaf.H (etaleGenericUnitQuotient M.C) 0,
      (M.finiteEtaleModel Y).genericUnitDivisorH0Equiv (finiteGenericUnitH0Pullback Y a) =
        Divisor.pullback Y.left.functionField (M.genericUnitDivisorH0Equiv a) := by
  intro hY algKY φ algFY hTower hFinite hIntegral hPrincipal a
  let N := M.finiteEtaleModel Y
  have : IsFiniteEtale (show Y.left ⟶ M.C from Y.hom) := Y.prop
  apply Finsupp.ext
  intro w
  let y : closedPoints Y.left := N.placeEquiv.symm w
  have hy : IsClosed ({Y.hom y.1} : Set M.C) := by
    rw [← Set.image_singleton]
    exact Y.hom.isClosedMap _ y.property
  let x : closedPoints M.C := ⟨Y.hom y.1, hy⟩
  have hw : N.placeOfPoint y = w := by
    rw [← N.placeEquiv_apply, Equiv.apply_symm_apply]
  have hr : w.restrict F = M.placeOfPoint x := by
    have h := M.restrict_placeOfPoint_finiteEtaleModel Y y hy
    rw [hw] at h
    exact h
  have hx : M.placeEquiv.symm (w.restrict F) = x := by
    rw [hr, ← M.placeEquiv_apply, Equiv.symm_apply_apply]
  have he : w.ramificationIndex F = 1 :=
    M.ramificationIndex_finiteEtaleModelFieldMap Y w
  rw [Divisor.pullback_apply, he, Nat.cast_one, one_mul]
  have hN := congrArg (fun d : Divisor K Y.left.functionField => d w)
    (N.genericUnitDivisorH0Equiv_apply (finiteGenericUnitH0Pullback Y a))
  have hNcoefficient := N.divisorSheafH0Equiv_apply
    (Sheaf.H.map (smoothCurveClosedPointDivisorGenericUnitIso N.toBase).inv 0
      (finiteGenericUnitH0Pullback Y a)) w
  have hM := congrArg (fun d : Divisor K F => d (w.restrict F))
    (M.genericUnitDivisorH0Equiv_apply a)
  have hMcoefficient := M.divisorSheafH0Equiv_apply
    (Sheaf.H.map (smoothCurveClosedPointDivisorGenericUnitIso M.toBase).inv 0 a)
    (w.restrict F)
  let sM := Sheaf.H.equiv₀.{u} (closedPointDivisorSheaf M.C)
    (MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) M.C)
    (Sheaf.H.map (smoothCurveClosedPointDivisorGenericUnitIso M.toBase).inv 0 a)
  have hpoint := congrArg
    (fun t : closedPoints M.C => closedPointDivisorGlobalCoefficient M.C t sM) hx
  have hNSmooth : SmoothOfRelativeDimension 1 N.toBase := N.smooth
  have hcoefficient := @finiteGenericUnitH0Pullback_coefficient
    K K (inferInstance : Field K) (inferInstance : Field K)
    M.C M.isIntegral (inferInstance : IsNormalIntegral M.C)
    Y (inferInstance : IsConnected Y) hY
    M.toBase M.smooth N.toBase hNSmooth a y x rfl
  exact hN.trans (hNcoefficient.trans
    (hcoefficient.trans (hM.trans (hMcoefficient.trans hpoint)).symm))

/-- Degree of the actual native quotient pullback is multiplied by
the degree of the canonical function-field extension. -/
theorem degree_genericUnitDivisorH0Equiv_finitePullback :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let _ : Algebra K Y.left.functionField :=
      (baseToFunctionField ((show Y.left ⟶ M.C from Y.hom) ≫ M.toBase)).toAlgebra
    ∀ a : Sheaf.H (etaleGenericUnitQuotient M.C) 0,
      Divisor.degree ((M.finiteEtaleModel Y).genericUnitDivisorH0Equiv
        (finiteGenericUnitH0Pullback Y a)) =
      ((let _ : Algebra M.C.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
        Module.finrank M.C.functionField Y.left.functionField) : ℤ) *
        Divisor.degree (M.genericUnitDivisorH0Equiv a) := by
  intro hY algKY a
  rw [M.genericUnitDivisorH0Equiv_finitePullback Y a]
  exact M.degree_finiteEtaleModel_pullback Y (M.genericUnitDivisorH0Equiv a)

end AlgebraicCurve.CurveModel
