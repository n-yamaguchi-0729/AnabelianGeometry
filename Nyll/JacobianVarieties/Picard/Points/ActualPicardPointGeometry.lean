/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicPointsEquivariance
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.AbelJacobiPicardRepresentability
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveCurveModelIsoPullbackFunctionFieldGermEq
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveSeparatingTranscendental

/-!
# Actual Picard point geometry over algebraically closed coefficients

The curve function field, its finite rational-function presentation, and the
equivariant Picard comparison are constructed from the original pointed
curve and its Picard representation. Neither a curve model nor an
Abel--Jacobi comparison is supplied as an extra hypothesis.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Picard

attribute [local instance]
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0

/-- Construct the actual geometric Picard comparison, with the original
coefficient action, from the original pointed curve and representation. -/
theorem exists_actual_picard_point_geometry
    {K L : Type} [Field K] [Field L] [IsAlgClosed L] [Algebra K L]
    {C : Scheme} (c : C ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) c)
    (D : RelativePic0Designation K c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase] :
    let Y := pullback c (specMap K L)
    let : IsIntegral Y := isIntegral_pullback_Spec_field K c (specMap K L)
    let F := Y.functionField
    let : Algebra L F := (baseToFunctionField (pullback.snd c (specMap K L))).toAlgebra
    let G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
    let hc : G.IsCommutative :=
      RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut c ε) hD
    ∃ (_ : IsCurveOver L F),
      (∃ z : F, Transcendental L z ∧
        FiniteDimensional (IntermediateField.adjoin L ({z} : Set F)) F) ∧
      ∃ e : Pic0 L F ≃+ G.AlgPoints hc L,
        ∀ σ : L ≃ₐ[K] L, ∃ g : SemilinearAut L F,
          SemilinearAut.baseAut g = σ.toRingEquiv ∧
          ∀ z : Pic0 L F, e (g • z) =
            RelativeGroupLaw.AlgPoints.map σ.toAlgHom (e z) := by
  intro Y hY F hLF G hc
  obtain ⟨hcurve, hft, M, eC, heC, _⟩ :=
    exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
      K c L (specMap K L)
  have : IsCurveOver L F := hcurve
  have : Algebra.EssFiniteType L F := hft
  obtain ⟨z, hz, hfin, _⟩ := IsCurveOver.exists_separating_transcendental (K := L) (F := F)
  obtain ⟨aj, _, hclass⟩ := exists_abelJacobi_of_representsRelSubPic K c ε D hD
  obtain ⟨e, _, he⟩ := exists_pic0_algPoints_equivariant_of_abelJacobi
    c ε D hD aj hclass M eC heC
  refine ⟨hcurve, ⟨z, hz, hfin⟩, e, ?_⟩
  intro σ
  obtain ⟨θ, g, _, _, hg, _, _, hge⟩ := he σ
  exact ⟨g, hg, hge⟩

end JacobianVarieties.Picard
