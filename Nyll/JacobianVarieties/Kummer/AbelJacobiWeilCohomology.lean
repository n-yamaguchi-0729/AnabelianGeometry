/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.JacobianVarieties.Kummer.JacobianWeilCharacters
public import Nyll.JacobianVarieties.Kummer.ActualWeilCohomologyPullback
public import Nyll.AlgebraicCurves.Models.ConstantExtension.ExtensionCoordinates
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Pic0EquivPointsPicardRepresentability
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Actual Weil classes and their Abel--Jacobi pullback

The same Picard representative, torsion coordinates and actual multiplication
characters construct derived H¹ classes whose pullbacks are the original curve
Kummer classes. All auxiliary generic and constant-extension data are supplied
from the curve; the index only needs to be invertible in the base field.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian EtaleFundamentalGroups.Cohomology
open GoodReductionJacobian.RelativeGroupLaw.UnitMultiplication
open JacobianVarieties.Picard.Proofs.Pic0PointsAbelJacobi.AlgebraicGeometry.RelPicard

namespace JacobianVarieties.Kummer

attribute [local instance] IsCurveOver.toHasPrincipalDivisors
  CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- Construct the actual Weil monodromy classes and prove their original
Abel--Jacobi pullback formula, with the same point and torsion identifications.
No comparison or finite-H¹ bijectivity is assumed. -/
theorem exists_abelJacobi_weil_cohomology_pullback
    {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [IsCurveOver K F] (M : CurveModel K F) [GeometricallyIntegral M.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    (D : RelativePic0Designation K M.toBase)
    (hD : RepresentsRelSubPic M.toBase ε (algEquivZeroCut M.toBase ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (aj : SchemeHomOver M.toBase D.toBase)
    (hclass : ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
      (x : SchemeHomOver t M.toBase),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M.toBase (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) :
    let : Algebra.EssFiniteType K F := DictGlue.essFiniteType_of_curveModel M
    let G := RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut M.toBase ε) hD
    let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut M.toBase ε) hD
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    let : ConnectedSpace D.P := GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
    let _ : Algebra K M.C.functionField := M.functionFieldAlgebra
    let Ω := AlgebraicClosure M.C.functionField
    let η := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω))
    let ξ := η ≫ M.C.fromSpecStalk (genericPoint M.C)
    ∃ e : Pic0 K F ≃+ G.AlgPoints hc K,
      (∀ x : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase,
        ∃ Dv : Divisor.degZero (K := K) (F := F),
          (Dv : Divisor K F) = Finsupp.single (M.pointEquivPlace x) 1 -
            Finsupp.single (M.pointEquivPlace ε) 1 ∧
          (RelativeGroupLaw.AlgPoints.toPoint (e (Pic0.mk Dv))).1 = x.1 ≫ aj.1) ∧
      ∃ τ : Pic0.torsion K F (n : ℕ) ≃+ ProCGroups.torsionLevel (G.AlgPoints hc K) n,
        (∀ x, (τ x).1 = e x.1) ∧
        (∀ x, (G.torsionLevelEquivSchemeKerPoints hc n (τ x)).1 ≫
          pullback.fst (G.schemeNsmul (n : ℕ)) (G.one (𝟙 (Spec (.of K)))).1 =
            (RelativeGroupLaw.AlgPoints.toPoint (e x.1)).1) ∧
        ∃ w : DivisorialWeilPairingData K F (n : ℕ),
          ∃ ν : Pic0.torsion K F (n : ℕ) →+
              Sheaf.H.{u} ((constantSheaf D.P.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1,
            (∀ (x : Pic0.torsion K F (n : ℕ))
              (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)),
              ((finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).1 (ν x)).toMul g :
                rootsOfUnity (n : ℕ) K).val.val =
                  w.pair x (τ.symm (monodromy G hc ⟨n, hn⟩ g))) ∧
            ∀ a : Pic0.torsion K F (n : ℕ),
              constantCohomologyPullback aj.1 A 1 (ν a) =
                M.kummerTorsionCohomology n hn ξ a := by
  intro hfinite G hc htop hdiscrete A hAtop hAdiscrete hconnected hbase Ω η ξ
  obtain ⟨e, hpoint, τ, hτ, hker, w, ν, hν⟩ :=
    exists_jacobian_weil_cohomology M ε D hD aj hclass n hn
  refine ⟨e, hpoint, τ, hτ, hker, w, ν, hν, ?_⟩
  apply M.with_constantExtension_coordinates Ω
  intro L hL hΩL hcurve hFL hKL htowerF htowerΩ hfg hfg' hgen ML eC heC hsq
  exact actual_abelJacobi_weil_cohomology_pullback M rfl
    hfg hfg' hgen ε D hD aj hclass ML eC heC hsq n hn e τ hτ hpoint w ν hν

end JacobianVarieties.Kummer
