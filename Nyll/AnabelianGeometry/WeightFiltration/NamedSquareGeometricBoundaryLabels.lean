/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineBoundaryPlaces
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationPairCrossRatio
import Nyll.AlgebraicCurves.FunctionFields.Rational.RatFuncPairSquareMap

/-! # One-sided geometric projection of the retained arithmetic labels

An E-label determines its actual geometric boundary place over κ. The place
formula of the actual square map and its omitted-boundary equality put the
restricted place in the original downstairs boundary. Source and target covers
can use this construction independently, before comparing their label maps.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace AnabelianGeometry.KummerTheory
open AnabelianGeometry.ProjectiveLine
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AlgebraicGeometry.ProjSpace

section GeometricProjection
variable (E κ : Type) [Field E] [Field κ] [Algebra E κ]
variable (t : Finset (Projectivization E (E × E)))
variable {U : Scheme} (j : U ⟶ (projectiveLineRatFuncModel κ).C)
variable (pκ : (projectiveLineRatFuncModel κ).C ⟶ (projectiveLineRatFuncModel κ).C)
variable (eκ : RatFunc κ ≃ₐ[κ] RatFunc κ)
variable (hplaces : ∀ y : closedPoints (projectiveLineRatFuncModel κ).C,
  ∃ hy : pκ.base y.val ∈ closedPoints (projectiveLineRatFuncModel κ).C,
    (projectiveLineRatFuncModel κ).placeOfPoint ⟨pκ.base y.val, hy⟩ =
      ((projectiveLineRatFuncModel κ).placeOfPoint y).restrictAlong
        (ratFuncPairSquareHom eκ) (ratFuncPairSquareHom_isIntegral eκ))
variable (hboundary : ∀ y : (projectiveLineRatFuncModel κ).C,
  y ∉ Set.range (rationalConfigurationBaseChangeChart E κ t) ↔
    pκ y ∉ Set.range j)

/-- The restricted place of the same E-label, with geometric boundary
membership proved from the actual square map. -/
def namedSquareGeometricBoundaryProjection (z : t) :
    (projectiveLineRatFuncModel κ).openBoundaryPlaces j := by
  let M := projectiveLineRatFuncModel κ
  let w := rationalConfigurationBoundaryPlace E κ t z
  let y : closedPoints M.C := M.placeEquiv.symm w.val
  refine ⟨w.val.restrictAlong (ratFuncPairSquareHom eκ)
    (ratFuncPairSquareHom_isIntegral eκ), ?_⟩
  obtain ⟨hy, hplace⟩ := hplaces y
  have hwy : M.placeOfPoint y = w.val :=
    (M.placeEquiv_apply y).symm.trans (M.placeEquiv.apply_symm_apply w.val)
  rw [hwy] at hplace
  have hcenter : M.placeEquiv.symm
      (w.val.restrictAlong (ratFuncPairSquareHom eκ)
        (ratFuncPairSquareHom_isIntegral eκ)) = ⟨pκ.base y.val, hy⟩ :=
    (congrArg M.placeEquiv.symm hplace.symm).trans
      ((congrArg M.placeEquiv.symm (M.placeEquiv_apply ⟨pκ.base y.val, hy⟩).symm).trans
        (M.placeEquiv.symm_apply_apply ⟨pκ.base y.val, hy⟩))
  change (M.placeEquiv.symm
    (w.val.restrictAlong (ratFuncPairSquareHom eκ)
      (ratFuncPairSquareHom_isIntegral eκ))).val ∉ Set.range j
  rw [hcenter]
  exact (hboundary y.val).mp w.property

/-- The one-sided supplier consumed by the actual chosen-inertia endpoint. -/
theorem namedSquareGeometricBoundaryProjection_restrict (z : t) :
    (rationalConfigurationBoundaryPlace E κ t z).val.restrictAlong
        (ratFuncPairSquareHom eκ) (ratFuncPairSquareHom_isIntegral eκ) =
      (namedSquareGeometricBoundaryProjection E κ t j pκ eκ hplaces hboundary z).val := rfl

/-- Homogeneous coordinates are extended only along E → κ; the upstairs
place remains that of the retained original label. -/
theorem namedSquareGeometricBoundaryProjection_coordinate (z : t) :
    (projectiveRatFuncPlace (rationalConfigurationProjectivePoint E κ z.val)).restrictAlong
        (ratFuncPairSquareHom eκ) (ratFuncPairSquareHom_isIntegral eκ) =
      (namedSquareGeometricBoundaryProjection E κ t j pκ eκ hplaces hboundary z).val := by
  rw [← rationalConfigurationBoundaryPlace_eq_projectiveRatFuncPlace E κ t z]
  exact namedSquareGeometricBoundaryProjection_restrict E κ t j pκ eκ hplaces hboundary z

end GeometricProjection

section OriginalLabels
variable (k E κ : Type) [Field k] [Field E] [Field κ] [Algebra k κ] [Algebra E κ]
variable (s : Finset (Projectivization k (k × k)))
variable (t : Finset (Projectivization E (E × E)))
variable (pκ : (projectiveLineRatFuncModel κ).C ⟶ (projectiveLineRatFuncModel κ).C)
variable (eκ : RatFunc κ ≃ₐ[κ] RatFunc κ)
variable (hplaces : ∀ y : closedPoints (projectiveLineRatFuncModel κ).C,
  ∃ hy : pκ.base y.val ∈ closedPoints (projectiveLineRatFuncModel κ).C,
    (projectiveLineRatFuncModel κ).placeOfPoint ⟨pκ.base y.val, hy⟩ =
      ((projectiveLineRatFuncModel κ).placeOfPoint y).restrictAlong
        (ratFuncPairSquareHom eκ) (ratFuncPairSquareHom_isIntegral eκ))
variable (hboundary : ∀ y : (projectiveLineRatFuncModel κ).C,
  y ∉ Set.range (rationalConfigurationBaseChangeChart E κ t) ↔
    pκ y ∉ Set.range (rationalConfigurationBaseChangeChart k κ s))

/-- Original downstairs labels recovered from the actual one-sided geometric
projection, without comparing two different square covers. -/
def namedSquareGeometricOriginalLabelProjection : t → s := fun z =>
  (rationalConfigurationBoundaryPlaceEquiv k κ s).symm
    (namedSquareGeometricBoundaryProjection E κ t
      (rationalConfigurationBaseChangeChart k κ s) pκ eκ hplaces hboundary z)

/-- Each retained upstairs label restricts to its own actual projected
original label; no source-target permutation occurs in this statement. -/
theorem namedSquareGeometricOriginalLabelProjection_restrict (z : t) :
    (rationalConfigurationBoundaryPlace E κ t z).val.restrictAlong
        (ratFuncPairSquareHom eκ) (ratFuncPairSquareHom_isIntegral eκ) =
      (rationalConfigurationBoundaryPlace k κ s
        (namedSquareGeometricOriginalLabelProjection k E κ s t pκ eκ hplaces hboundary z)).val := by
  have h := congrArg Subtype.val
    ((rationalConfigurationBoundaryPlaceEquiv k κ s).apply_symm_apply
      (namedSquareGeometricBoundaryProjection E κ t
        (rationalConfigurationBaseChangeChart k κ s) pκ eκ hplaces hboundary z))
  exact (namedSquareGeometricBoundaryProjection_restrict E κ t
    (rationalConfigurationBaseChangeChart k κ s) pκ eκ hplaces hboundary z).trans h.symm

end OriginalLabels
end AlgebraicGeometry.ProjSpace
