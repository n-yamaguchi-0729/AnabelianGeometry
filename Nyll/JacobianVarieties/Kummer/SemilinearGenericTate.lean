/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.SemilinearGenericMonodromy
import Nyll.AlgebraicCurves.Models.ConstantExtension.ExtensionCoordinates
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianTateBasePoint
import Nyll.ProCGroups.Abelian.FullTateModuleMap
import Nyll.JacobianVarieties.Picard.Torsion.TorsionAlgebraicPoints

/-!
# Semilinear naturality of the existing full Tate comparison

The proved finite-coordinate formula identifies transport on the existing
full Tate module, using one specified Picard/points comparison at all levels.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Kummer

open JacobianVarieties.Picard.Proofs.Pic0PointsAbelJacobi.AlgebraicGeometry.RelPicard

attribute [local instance] IsCurveOver.toHasPrincipalDivisors

/-- Semilinear conjugation commutes with the existing full Tate comparison,
in the coordinates of the same specified Picard/points equivalence.
The auxiliary constant-extension model is constructed internally. -/
theorem actual_abelJacobi_generic_fullTate_semilinear
    {K F₀ : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F₀] [Algebra K F₀] [IsCurveOver K F₀]
    (M₀ : CurveModel K F₀)
    [Algebra K M₀.C.functionField]
    (hbase : algebraMap K M₀.C.functionField = baseToFunctionField M₀.toBase)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra M₀.C.functionField Ω] [IsScalarTower K M₀.C.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M₀.C.functionField Ω]
    [IsProper M₀.toBase] [SmoothOfRelativeDimension 1 M₀.toBase] [GeometricallyIntegral M₀.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase)
    (D : RelativePic0Designation K M₀.toBase)
    (hD : RepresentsRelSubPic M₀.toBase ε (algEquivZeroCut M₀.toBase ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (aj : SchemeHomOver M₀.toBase D.toBase)
    (hclass : ∀ (L : Type) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
      (x : SchemeHomOver t M₀.toBase),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M₀.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M₀.toBase (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    :
    let G := RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    let η := Spec.map (CommRingCat.ofHom (algebraMap M₀.C.functionField Ω))
    let q := M₀.C.fromSpecStalk (genericPoint M₀.C)
    ∀ (e₀ : Pic0 K F₀ ≃+ G.AlgPoints hc K),
      (∀ v : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase,
        ∃ Dv : Divisor.degZero (K := K) (F := F₀),
          (Dv : Divisor K F₀) = Finsupp.single (M₀.pointEquivPlace v) 1 -
            Finsupp.single (M₀.pointEquivPlace ε) 1 ∧
          (RelativeGroupLaw.AlgPoints.toPoint (e₀ (Pic0.mk Dv))).1 = v.1 ≫ aj.1) →
    ∀ (g : SemilinearAut K F₀) (φ : M₀.C.functionField ≃+* M₀.C.functionField)
      (_hφ : ∀ r : F₀, φ (M₀.ffEquiv r) = M₀.ffEquiv (SemilinearAut.toRingAut g r))
      (a : Ω ≃+* Ω)
      (ha : ∀ r : M₀.C.functionField,
        a (algebraMap M₀.C.functionField Ω r) = algebraMap M₀.C.functionField Ω (φ r))
      (σ : Ω ≃ₐ[M₀.C.functionField] Ω),
      let μ := fun ρ : Ω ≃ₐ[M₀.C.functionField] Ω =>
        G.fundamentalGroupEquivFullTateAt hc (η ≫ q ≫ aj.1)
          (FiniteEtale.fundamentalGroupHom (q ≫ aj.1) η
            (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M₀.C.functionField] Ω) ρ))
      μ (KummerTheory.semilinearGaloisConjugate φ a ha σ) =
        Multiplicative.ofAdd (ProCGroups.FullTateModule.map
          (e₀.toAddMonoidHom.comp
            ((DistribSMul.toAddMonoidHom (Pic0 K F₀) g).comp e₀.symm.toAddMonoidHom))
          (Multiplicative.toAdd (μ σ))) := by
  have : Algebra.EssFiniteType K F₀ := DictGlue.essFiniteType_of_curveModel M₀
  apply M₀.with_constantExtension_coordinates Ω
  intro F hF hΩF hcurve hF₀F hKF htower₀ htowerΩ hfg hfg' hgen M eC heC hsq
    G hc η q e₀ hpoint g φ hφ a ha σ μ
  have : ConnectedSpace D.P :=
    GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
  let b : FiniteEtale.fiber (η ≫ q ≫ aj.1) ≅
      FiniteEtale.fiber (G.one (𝟙 (Spec (.of K)))).1 :=
    Classical.choice (FiniteEtale.nonempty_fiber_iso _ _)
  apply Multiplicative.toAdd.injective
  apply ProCGroups.FullTateModule.ext
  intro n
  have hn : IsUnit ((n : ℕ) : K) := isUnit_iff_ne_zero.mpr
    (Nat.cast_ne_zero.mpr n.ne_zero)
  let τn := JacobianVarieties.Picard.torsionEquivOfAddEquiv e₀ n
  have hτn (t : Pic0.torsion K F₀ n) : (τn t).val = e₀ t.val := rfl
  obtain ⟨w⟩ := Pic0.nonempty_divisorialWeilPairingData_of_isAlgClosed K F₀ hfg (n : ℕ)
  let z := b.inv.app (G.multiplicationCover hc n) (G.multiplicationCoverUnit hc n)
  have hmono := actual_abelJacobi_generic_monodromy_semilinear
    M₀ hbase hfg hfg' hgen ε D hD aj hclass M eC heC hsq n hn w
    e₀ τn hτn hpoint b z g φ hφ a ha σ
  have hp (ρ : Ω ≃ₐ[M₀.C.functionField] Ω) :
      ProCGroups.FullTateModule.projection (G.AlgPoints hc K) n
        (Multiplicative.toAdd (μ ρ)) =
      G.multiplicationMonodromy hc n
        (continuousConjAut b (FiniteEtale.fundamentalGroupHom (q ≫ aj.1) η
          (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M₀.C.functionField] Ω) ρ))) :=
    G.fundamentalGroupEquivFullTateAt_projection hc (η ≫ q ≫ aj.1) b _ n
  have hv (y : ProCGroups.torsionLevel (G.AlgPoints hc K) n) :
      e₀ (τn.symm y).val = y.val :=
    (hτn (τn.symm y)).symm.trans (congrArg Subtype.val (τn.apply_symm_apply y))
  have ht (y : ProCGroups.torsionLevel (G.AlgPoints hc K) n) :
      (τn.symm y).val = e₀.symm y.val := by
    apply e₀.injective
    exact (hv y).trans (e₀.apply_symm_apply y.val).symm
  have heq := congrArg (fun x : Pic0.torsion K F₀ n => e₀ x.val) hmono
  rw [SemilinearAut.coe_torsion_smul, hv, ht] at heq
  change (ProCGroups.FullTateModule.projection (G.AlgPoints hc K) n
      (Multiplicative.toAdd (μ (KummerTheory.semilinearGaloisConjugate φ a ha σ)))).val =
    e₀ (g • e₀.symm (ProCGroups.FullTateModule.projection (G.AlgPoints hc K) n
      (Multiplicative.toAdd (μ σ))).val)
  rw [hp, hp]
  exact heq

end JacobianVarieties.Kummer
