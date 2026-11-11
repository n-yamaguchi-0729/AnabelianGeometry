/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.JacobianVarieties.Kummer.ActualCohomologyPullback
public import Nyll.AlgebraicCurves.Models.ConstantExtension.ExtensionCoordinates
public import Nyll.JacobianVarieties.Kummer.JacobianWeilCharacters
public import Nyll.JacobianVarieties.Kummer.JacobianWeilCohomologyBijective
public import Nyll.AlgebraicCurves.Models.Kummer.DivisorClassCohomologyComparison
public import Nyll.JacobianVarieties.Kummer.CohomologyPullbackCharacters
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericPointCharacterDetection
public import Nyll.EtaleFundamentalGroups.Cohomology.H1CharacterComposition
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks

/-!
# Actual Abel--Jacobi pullback on finite-coefficient H¹

The geometric generic Weil--Kummer identity determines the actual global
derived-cohomology pullback. The auxiliary geometric model is supplied here
with its germ and field-generation data; construction of this model is separate.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve NeronModelInfra GoodReductionJacobian
open EtaleFundamentalGroups.Cohomology

namespace JacobianVarieties.Kummer

open JacobianVarieties.Picard.Proofs.Pic0PointsAbelJacobi.AlgebraicGeometry.RelPicard

attribute [local instance] IsCurveOver.toHasPrincipalDivisors

/-- The actual Abel--Jacobi pullback is bijective on finite constant
roots-of-unity H¹. All auxiliary constant-extension coordinates are
constructed from the original smooth proper geometrically integral curve.
The multiplication index need only be invertible; the constants may have positive characteristic. -/
theorem abelJacobi_finiteH1Pullback_bijective
    {K F₀ : Type u} [Field K] [IsAlgClosed K]
    [Field F₀] [Algebra K F₀] [IsCurveOver K F₀]
    (M₀ : CurveModel K F₀)
    [GeometricallyIntegral M₀.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase)
    (D : RelativePic0Designation K M₀.toBase)
    (hD : RepresentsRelSubPic M₀.toBase ε (algEquivZeroCut M₀.toBase ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (aj : SchemeHomOver M₀.toBase D.toBase)
    (hclass : ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
      (x : SchemeHomOver t M₀.toBase),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M₀.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M₀.toBase (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) :
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let : ConnectedSpace D.P :=
      GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
    Function.Bijective (constantCohomologyPullback aj.1 A 1) := by
  intro A hconnected
  classical
  let : Algebra K M₀.C.functionField := M₀.functionFieldAlgebra
  let Ω := AlgebraicClosure M₀.C.functionField
  let : Algebra K Ω := inferInstance
  have : IsScalarTower K M₀.C.functionField Ω := inferInstance
  have : Algebra.EssFiniteType K F₀ := DictGlue.essFiniteType_of_curveModel M₀
  apply M₀.with_constantExtension_coordinates Ω
  intro F hF hΩF hcurve hF₀F hKF htower₀ htowerΩ hfg hfg' hgen M eC heC hsq
  exact actual_abelJacobi_finiteH1Pullback_bijective M₀ rfl
    hfg hfg' hgen ε D hD aj hclass M eC heC hsq n hn

end JacobianVarieties.Kummer
