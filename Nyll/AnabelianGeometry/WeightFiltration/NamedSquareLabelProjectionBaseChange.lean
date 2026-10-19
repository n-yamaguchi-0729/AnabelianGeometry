/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareBoundaryProjection
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareGeometricBoundaryLabels
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineBoundary
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineStandardPlace

/-! # Named Square Label Projection Base Change -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace AnabelianGeometry.ProjectiveLine
open AnabelianGeometry.KummerTheory
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AlgebraicGeometry.ProjSpace

theorem rationalConfigurationGeometricPoint_coefficient_tower
    (k E κ : Type) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    (a : Projectivization k (k × k)) :
    map E κ 1 (rationalConfigurationGeometricPoint k κ a) =
      rationalConfigurationGeometricPoint k E a := by
  have hform : MvPolynomial.map (algebraMap E κ)
      (punctureForm (extendedPunctureCoordinates k E a)) =
      punctureForm (extendedPunctureCoordinates k κ a) := by
    simp only [punctureForm, extendedPunctureCoordinates, map_sub, map_mul,
      MvPolynomial.map_C, MvPolynomial.map_X,
      ← IsScalarTower.algebraMap_apply k E κ]
  apply eq_of_punctureForm_mem (extendedPunctureCoordinates k E a)
    (extendedPunctureCoordinates_ne_zero k E a)
  · change MvPolynomial.map (algebraMap E κ)
      (punctureForm (extendedPunctureCoordinates k E a)) ∈
        (rationalConfigurationGeometricPoint k κ a).asHomogeneousIdeal
    rw [hform]
    exact punctureForm_mem_rationalPuncturePoint _ _
  · exact punctureForm_mem_rationalPuncturePoint _ _

private theorem namedSquare_modelPlace_center
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) (y : closedPoints M.C) :
    (M.placeEquiv.symm (M.placeOfPoint y)).val = y.val := by
  rw [← M.placeEquiv_apply, M.placeEquiv.symm_apply_apply]

section ProjectionCenters
variable (k E : Type) [Field k] [Field E] [Algebra k E]
variable (s : Finset (Projectivization k (k × k)))
variable (t : Finset (Projectivization E (E × E)))
variable (pE : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
variable (eE : RatFunc E ≃ₐ[E] RatFunc E)
variable (hplacesE : ∀ y : closedPoints (projectiveLineRatFuncModel E).C,
  ∃ hy : pE.base y.val ∈ closedPoints (projectiveLineRatFuncModel E).C,
    (projectiveLineRatFuncModel E).placeOfPoint ⟨pE.base y.val, hy⟩ =
      ((projectiveLineRatFuncModel E).placeOfPoint y).restrictAlong
        (ratFuncPairSquareHom eE) (ratFuncPairSquareHom_isIntegral eE))
variable (ht : ∀ z, z ∈ t ↔ projectiveRationalPoint z ∉ Set.range
  (CategoryTheory.Limits.pullback.fst pE (rationalConfigurationBaseChangeChart k E s)))

theorem namedSquareOriginalLabelProjection_center (z : t) :
    rationalConfigurationGeometricPoint k E
      (namedSquareOriginalLabelProjection k E s pE eE hplacesE t ht z).val =
        pE (projectiveRationalPoint z.val) := by
  let M := projectiveLineRatFuncModel E
  let y : closedPoints M.C := ⟨projectiveRationalPoint z.val,
    isClosed_singleton_rationalPuncturePoint z.val.rep z.val.rep_nonzero⟩
  obtain ⟨hy, hplace⟩ := hplacesE y
  have hz : M.placeOfPoint y = projectiveRatFuncPlace z.val :=
    projectiveLineRatFuncModel_placeOfPoint_projectiveRationalPoint E z.val
  rw [hz] at hplace
  have hproj := namedSquareOriginalLabelProjection_place k E s pE eE hplacesE t ht z
  have heq := hplace.trans hproj.symm
  have hc := congrArg (fun v : Place E (RatFunc E) => (M.placeEquiv.symm v).val) heq
  rw [namedSquare_modelPlace_center, rationalConfigurationBoundaryPlace_center] at hc
  exact hc.symm

end ProjectionCenters

section GeometricCenter
variable (k E κ : Type) [Field k] [Field E] [Field κ] [Algebra k κ] [Algebra E κ]
variable (s : Finset (Projectivization k (k × k)))
variable (t : Finset (Projectivization E (E × E)))
variable (pκ : (projectiveLineRatFuncModel κ).C ⟶ (projectiveLineRatFuncModel κ).C)
variable (eκ : RatFunc κ ≃ₐ[κ] RatFunc κ)
variable (hplacesκ : ∀ y : closedPoints (projectiveLineRatFuncModel κ).C,
  ∃ hy : pκ.base y.val ∈ closedPoints (projectiveLineRatFuncModel κ).C,
    (projectiveLineRatFuncModel κ).placeOfPoint ⟨pκ.base y.val, hy⟩ =
      ((projectiveLineRatFuncModel κ).placeOfPoint y).restrictAlong
        (ratFuncPairSquareHom eκ) (ratFuncPairSquareHom_isIntegral eκ))
variable (hboundaryκ : ∀ y : (projectiveLineRatFuncModel κ).C,
  y ∉ Set.range (rationalConfigurationBaseChangeChart E κ t) ↔
    pκ y ∉ Set.range (rationalConfigurationBaseChangeChart k κ s))

theorem namedSquareGeometricOriginalLabelProjection_center (z : t) :
    rationalConfigurationGeometricPoint k κ
      (namedSquareGeometricOriginalLabelProjection k E κ s t pκ eκ hplacesκ hboundaryκ z).val =
        pκ (rationalConfigurationGeometricPoint E κ z.val) := by
  let M := projectiveLineRatFuncModel κ
  let w := rationalConfigurationBoundaryPlace E κ t z
  let y : closedPoints M.C := M.placeEquiv.symm w.val
  obtain ⟨hy, hplace⟩ := hplacesκ y
  have hwy : M.placeOfPoint y = w.val :=
    (M.placeEquiv_apply y).symm.trans (M.placeEquiv.apply_symm_apply w.val)
  have hproj := namedSquareGeometricOriginalLabelProjection_restrict
    k E κ s t pκ eκ hplacesκ hboundaryκ z
  have heq := hplace.trans
    ((congrArg (fun V : Place κ (RatFunc κ) =>
      V.restrictAlong (ratFuncPairSquareHom eκ)
        (ratFuncPairSquareHom_isIntegral eκ)) hwy).trans hproj)
  have hc := congrArg (fun v : Place κ (RatFunc κ) => (M.placeEquiv.symm v).val) heq
  have hc' : pκ y.val = (M.placeEquiv.symm
      (rationalConfigurationBoundaryPlace k κ s
        (namedSquareGeometricOriginalLabelProjection
          k E κ s t pκ eκ hplacesκ hboundaryκ z)).val).val :=
    (namedSquare_modelPlace_center M ⟨pκ y.val, hy⟩).symm.trans hc
  have hycenter : y.val = rationalConfigurationGeometricPoint E κ z.val :=
    rationalConfigurationBoundaryPlace_center E κ t z
  exact (rationalConfigurationBoundaryPlace_center k κ s _).symm.trans
    (hc'.symm.trans (congrArg pκ hycenter))

end GeometricCenter

theorem namedSquareGeometricOriginalLabelProjection_eq_original
    (k E κ : Type) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    (s : Finset (Projectivization k (k × k)))
    (t : Finset (Projectivization E (E × E)))
    (pE : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
    (pκ : (projectiveLineRatFuncModel κ).C ⟶ (projectiveLineRatFuncModel κ).C)
    (hcoeff : pκ ≫ map E κ 1 = map E κ 1 ≫ pE)
    (eE : RatFunc E ≃ₐ[E] RatFunc E) (eκ : RatFunc κ ≃ₐ[κ] RatFunc κ)
    (hplacesE : ∀ y : closedPoints (projectiveLineRatFuncModel E).C,
      ∃ hy : pE.base y.val ∈ closedPoints (projectiveLineRatFuncModel E).C,
        (projectiveLineRatFuncModel E).placeOfPoint ⟨pE.base y.val, hy⟩ =
          ((projectiveLineRatFuncModel E).placeOfPoint y).restrictAlong
            (ratFuncPairSquareHom eE) (ratFuncPairSquareHom_isIntegral eE))
    (hplacesκ : ∀ y : closedPoints (projectiveLineRatFuncModel κ).C,
      ∃ hy : pκ.base y.val ∈ closedPoints (projectiveLineRatFuncModel κ).C,
        (projectiveLineRatFuncModel κ).placeOfPoint ⟨pκ.base y.val, hy⟩ =
          ((projectiveLineRatFuncModel κ).placeOfPoint y).restrictAlong
            (ratFuncPairSquareHom eκ) (ratFuncPairSquareHom_isIntegral eκ))
    (ht : ∀ z, z ∈ t ↔ projectiveRationalPoint z ∉ Set.range
      (CategoryTheory.Limits.pullback.fst pE (rationalConfigurationBaseChangeChart k E s)))
    (hboundaryκ : ∀ y : (projectiveLineRatFuncModel κ).C,
      y ∉ Set.range (rationalConfigurationBaseChangeChart E κ t) ↔
        pκ y ∉ Set.range (rationalConfigurationBaseChangeChart k κ s))
    (z : t) :
    namedSquareGeometricOriginalLabelProjection k E κ s t pκ eκ hplacesκ hboundaryκ z =
      namedSquareOriginalLabelProjection k E s pE eE hplacesE t ht z := by
  apply Subtype.ext
  apply rationalConfigurationGeometricPoint_injective k E
  have hcoeffPoint : map E κ 1 (pκ (rationalConfigurationGeometricPoint E κ z.val)) =
      pE (map E κ 1 (rationalConfigurationGeometricPoint E κ z.val)) :=
    congrArg (fun f : (projectiveLineRatFuncModel κ).C ⟶ (projectiveLineRatFuncModel E).C =>
      f (rationalConfigurationGeometricPoint E κ z.val)) hcoeff
  exact (rationalConfigurationGeometricPoint_coefficient_tower k E κ _).symm.trans
    ((congrArg (map E κ 1)
      (namedSquareGeometricOriginalLabelProjection_center
        k E κ s t pκ eκ hplacesκ hboundaryκ z)).trans
      (hcoeffPoint.trans ((congrArg pE (map_rationalConfigurationGeometricPoint E κ z.val)).trans
        (namedSquareOriginalLabelProjection_center k E s t pE eE hplacesE ht z).symm)))

end AlgebraicGeometry.ProjSpace
