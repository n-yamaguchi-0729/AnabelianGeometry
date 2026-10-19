/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.ProjectiveSpace.ProjectiveLineRatFuncBaseChange
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineRatFuncModel

/-! # Coefficient-extension comparison for the literal rational CurveModels -/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open scoped RatFunc
namespace AlgebraicGeometry.ProjSpace
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
variable (k κ : Type) [Field k] [Field κ] [Algebra k κ]
local instance literalBaseChange_projectiveLine_integral (F : Type) [Field F] :
    IsIntegral (Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) F)) :=
  projectiveSpace_isIntegral F 1

/-- The field comparison used by the literal arithmetic/geometric models. -/
theorem projectiveLineRatFuncModel_coefficientMap :
    ((map k κ 1).functionFieldMap (projectiveLineMap_denseRange k κ)).comp
        (projectiveLineRatFuncModel k).ffEquiv.toRingHom =
      (projectiveLineRatFuncModel κ).ffEquiv.toRingHom.comp
        (algebraMap (RatFunc k) (RatFunc κ)) := by
  ext z
  exact projectiveLineRatFuncEquiv_coefficientMap k κ z

/-- Supplies the concrete hchart for the canonical literal Proj models;
it is proved from the x0/x1 chart, rather than requested as input. -/
theorem projectiveLineRatFuncModel_baseChange_hchart (z : RatFunc k) :
    Scheme.Hom.functionFieldMap
      ((isPullback_map k κ 1).isoPullback.hom ≫
        CategoryTheory.Limits.pullback.fst (π k 1)
          (Spec.map (CommRingCat.ofHom (algebraMap k κ))))
      (projectiveLineBaseChangeProjection_denseRange k κ)
        (projectiveLineRatFuncEquiv k z) =
      (projectiveLineRatFuncModel κ).ffEquiv
        (algebraMap (RatFunc k) (RatFunc κ) z) := by
  have h := functionFieldMap_eq_of_eq
    ((isPullback_map k κ 1).isoPullback.hom ≫
      CategoryTheory.Limits.pullback.fst (π k 1)
        (Spec.map (CommRingCat.ofHom (algebraMap k κ))))
    (map k κ 1) (projectiveLineBaseChangeProjection_denseRange k κ)
    (projectiveLineMap_denseRange k κ)
    (isPullback_map k κ 1).isoPullback_hom_fst
  rw [h]
  exact projectiveLineRatFuncEquiv_coefficientMap k κ z

end AlgebraicGeometry.ProjSpace
