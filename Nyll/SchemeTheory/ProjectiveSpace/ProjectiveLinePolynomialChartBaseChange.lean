/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_isPullback_map.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/
import Nyll.SchemeTheory.ProjectiveSpace.ProjectiveLineRatFuncCoordinate
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # The actual polynomial-chart coefficient-extension square

Chart 1 is the canonical x0/x1 chart constructed in ProjectiveLineRatFuncModel.
Its coefficient-extension square is proved here from the existing homogeneous
localization map: constants are mapped by awayMapX_algebraMap and the coordinate
is mapped by awayMapX_ratio. No comparison square is assumed.

The first geometric lemma extracts the dependent transport argument from the
BaseChange.lean isPullback_map' proof. Function-field promotion is a
separate task and is not asserted in this file.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open HomogeneousLocalization
open AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ]
local notation "𝒜k" => MvPolynomial.homogeneousSubmodule (Fin 2) k
local notation "𝒜κ" => MvPolynomial.homogeneousSubmodule (Fin 2) κ
local notation "Ak" => Away 𝒜k (MvPolynomial.X (1 : Fin 2))
local notation "Aκ" => Away 𝒜κ (MvPolynomial.X (1 : Fin 2))

/-- The actual chart-local homogeneous coefficient map commutes with the
actual morphism of projective lines. -/
theorem projectiveLineAwayι_comp_map :
    Proj.awayι 𝒜κ (MvPolynomial.X (1 : Fin 2)) (X_mem_one κ 1 1) one_pos ≫ map k κ 1 =
      Spec.map (CommRingCat.ofHom (awayMapX k κ 1 1)) ≫
        Proj.awayι 𝒜k (MvPolynomial.X (1 : Fin 2)) (X_mem_one k 1 1) one_pos := by
  rw [map_eq]
  have haux : ∀ {y : MvPolynomial (Fin 2) κ}
      (h : (mvMapGraded k κ 1) (MvPolynomial.X (1 : Fin 2)) = y) (hy : y ∈ 𝒜κ 1),
      Proj.awayι 𝒜κ y hy one_pos ≫
          Proj.map (mvMapGraded k κ 1) (irrelevant_le_map_mvMapGraded k κ 1) =
        Spec.map (CommRingCat.ofHom
            (h ▸ HomogeneousLocalization.Away.map (mvMapGraded k κ 1)
              (MvPolynomial.X (1 : Fin 2)))) ≫
          Proj.awayι 𝒜k (MvPolynomial.X (1 : Fin 2)) (X_mem_one k 1 1) one_pos := by
    intro y h hy
    subst h
    exact Proj.awayι_comp_map (mvMapGraded k κ 1)
      (irrelevant_le_map_mvMapGraded k κ 1) one_pos (MvPolynomial.X (1 : Fin 2))
      (X_mem_one k 1 1)
  exact haux (mvMapGraded_X k κ 1 1) (X_mem_one κ 1 1)

/-- The canonical polynomial-coordinate equivalence maps both coefficients
and x0/x1 along the actual homogeneous coefficient map. -/
theorem projectiveLinePolynomialChartEquiv_awayMapX :
    (awayMapX k κ 1 1).comp (projectiveLinePolynomialChartEquiv k).toRingHom =
      (projectiveLinePolynomialChartEquiv κ).toRingHom.comp
        (Polynomial.mapRingHom (algebraMap k κ)) := by
  apply Polynomial.ringHom_ext
  · intro a
    change awayMapX k κ 1 1 (projectiveLinePolynomialChartEquiv k (Polynomial.C a)) =
      projectiveLinePolynomialChartEquiv κ ((Polynomial.C a).map (algebraMap k κ))
    calc
      _ = awayMapX k κ 1 1
          (algebraMap k
            (Away 𝒜k (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k)) a) :=
        congrArg (awayMapX k κ 1 1) ((projectiveLinePolynomialChartEquiv k).commutes a)
      _ = algebraMap κ
          (Away 𝒜κ (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) κ))
          (algebraMap k κ a) :=
        DFunLike.congr_fun (awayMapX_algebraMap k κ 1 1) a
      _ = projectiveLinePolynomialChartEquiv κ
          (Polynomial.C (algebraMap k κ a)) :=
        ((projectiveLinePolynomialChartEquiv κ).commutes (algebraMap k κ a)).symm
      _ = _ := by rw [Polynomial.map_C]
  · change awayMapX k κ 1 1 (projectiveLinePolynomialChartEquiv k Polynomial.X) =
      projectiveLinePolynomialChartEquiv κ (Polynomial.X.map (algebraMap k κ))
    rw [Polynomial.map_X, projectiveLinePolynomialChartEquiv_X,
      projectiveLinePolynomialChartEquiv_X, awayMapX_ratio]

/-- The contravariant coordinate equation needed after applying Spec. -/
theorem projectiveLinePolynomialChartEquiv_symm_comp_awayMapX :
    (projectiveLinePolynomialChartEquiv κ).symm.toRingHom.comp (awayMapX k κ 1 1) =
      (Polynomial.mapRingHom (algebraMap k κ)).comp
        (projectiveLinePolynomialChartEquiv k).symm.toRingHom := by
  apply RingHom.ext
  intro z
  apply (projectiveLinePolynomialChartEquiv κ).injective
  change projectiveLinePolynomialChartEquiv κ
      ((projectiveLinePolynomialChartEquiv κ).symm (awayMapX k κ 1 1 z)) =
    projectiveLinePolynomialChartEquiv κ
      (((projectiveLinePolynomialChartEquiv k).symm z).map (algebraMap k κ))
  rw [AlgEquiv.apply_symm_apply]
  have h := DFunLike.congr_fun (projectiveLinePolynomialChartEquiv_awayMapX k κ)
    ((projectiveLinePolynomialChartEquiv k).symm z)
  change awayMapX k κ 1 1
      (projectiveLinePolynomialChartEquiv k ((projectiveLinePolynomialChartEquiv k).symm z)) =
    projectiveLinePolynomialChartEquiv κ
      (((projectiveLinePolynomialChartEquiv k).symm z).map (algebraMap k κ)) at h
  simpa only [AlgEquiv.apply_symm_apply] using h

/-- The actual polynomial standard charts commute with coefficient
extension of the actual projective-line schemes. -/
theorem projectiveLinePolynomialChart_comp_map :
    projectiveLinePolynomialChart κ ≫ map k κ 1 =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k κ))) ≫
        projectiveLinePolynomialChart k := by
  unfold projectiveLinePolynomialChart
  rw [Category.assoc, projectiveLineAwayι_comp_map]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [projectiveLinePolynomialChartEquiv_symm_comp_awayMapX]
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

end AlgebraicGeometry.ProjSpace
