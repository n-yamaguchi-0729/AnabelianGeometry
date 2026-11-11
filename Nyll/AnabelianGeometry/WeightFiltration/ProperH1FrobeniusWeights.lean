/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.WeightFiltration.KummerFrobenius
public import Nyll.AnabelianGeometry.WeightFiltration.TateFrobeniusFixed
public import Nyll.EtaleCohomology.Frobenius.AdicH1Functoriality
public import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicPointsEquivariance
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.AbelJacobiPicardRepresentability
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Existence
public import Nyll.AbelianVarieties.Tate.Representation

/-!
# Frobenius weight separation on the original proper H¹

The pointed assertion constructs the Picard representative, Abel–Jacobi map,
and coefficient-equivariant point comparison. The same semilinear action is
then used in the Kummer comparison. Rational Tate fixed-vector vanishing
therefore rules out the cardinality eigenvalue for inverse coefficient twist.

The rational point in this leaf is genuine geometric data. Removing it by
the existing finite-extension presentation is a separate descent step.

-/

@[expose] public section

universe uGeom uField

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open EtaleCohomology.Classical NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

namespace AnabelianGeometry.FiniteField

variable (k : Type uGeom) [Field k] [Fintype k]
  {K : Type uGeom} {F : Type uField} [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  [Field F] [Algebra K F] [Algebra.EssFiniteType K F] [IsCurveOver K F]
  {C : Scheme.{uGeom}} (c : C ⟶ Spec (CommRingCat.of k))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
  (M : CurveModel K F) (eC : M.C ≅ pullback c (specMap k K))
  (heC : eC.hom ≫ pullback.snd c (specMap k K) = M.toBase)
  (p : ℕ+) [Fact (p : ℕ).Prime] (hp : IsUnit ((p : ℕ) : K))
  (r : ℕ) (hr : r ≠ 0) (θ : M.C ≅ M.C)
  (hproj : θ.hom ≫ eC.hom ≫ pullback.fst c (specMap k K) =
    eC.hom ≫ pullback.fst c (specMap k K))
  (hbase : θ.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom
    (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r).toRingHom))

include ε heC hp hr hproj hbase

/-- Positive coefficient Frobenius, multiplied by the cardinality, has no
fixed vector on actual proper H¹. All Picard and Tate comparisons are
constructed from the curve and the specified rational point. -/
theorem properRationalH1_eq_zero_of_coefficientFrobenius
    (v : rationalEllAdicCohomology (p : ℕ) M.C 1)
    (hv : v = Fintype.card k ^ r • rationalEllAdicPullback θ.hom (p : ℕ) 1 v) :
    v = 0 := by
  obtain ⟨D, ⟨hD⟩, hsD, hpD, hgD⟩ := exists_representsRelSubPic_of_field k c ε
  have : Smooth D.toBase := hsD
  have : IsProper D.toBase := hpD
  have : GeometricallyConnected D.toBase := hgD
  have : CompactSpace D.P := QuasiCompact.compactSpace_of_compactSpace D.toBase
  obtain ⟨aj, _, hclass⟩ := exists_abelJacobi_of_representsRelSubPic k c ε D hD
  let G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
  let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
    (P := algEquivZeroGroupCut c ε) hD
  obtain ⟨e, _, he⟩ := JacobianVarieties.Picard.exists_pic0_algPoints_equivariant_of_abelJacobi
    c ε D hD aj hclass M eC heC
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r
  obtain ⟨θ', g, hproj', hbase', hg, hfun, _, hge⟩ := he σ
  have hθ : θ'.hom = θ.hom := by
    apply (cancel_mono eC.hom).1
    apply pullback.hom_ext
    · simpa only [Category.assoc] using hproj'.trans hproj.symm
    · simp only [Category.assoc, heC]
      exact hbase'.trans hbase.symm
  let T := TateModule.map (p : ℕ)
    (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) σ.toAlgHom)
  let E := (TateModule.congr (p : ℕ) e).symm.trans (properKummerTateAdicLinearEquiv M p hp)
  have hE (x : TateModule (p : ℕ) (G.AlgPoints hc K)) :
      E (T x) = Fintype.card k ^ r • ellAdicPullback θ.hom (p : ℕ) 1 (E x) := by
    let y := (TateModule.congr (p : ℕ) e).symm x
    have ht : (TateModule.congr (p : ℕ) e)
        (TateModule.map (p : ℕ) (DistribSMul.toAddMonoidHom (Pic0 K F) g) y) = T x := by
      have h := TateModule.map_rep (p : ℕ) e.toAddMonoidHom g σ hge y
      change (TateModule.congr (p : ℕ) e)
          (TateModule.map (p : ℕ) (DistribSMul.toAddMonoidHom (Pic0 K F) g) y) =
        T ((TateModule.congr (p : ℕ) e) y) at h
      exact h.trans (congrArg T ((TateModule.congr (p : ℕ) e).apply_symm_apply x))
    change properKummerTateAdicLinearEquiv M p hp
        ((TateModule.congr (p : ℕ) e).symm (T x)) =
      Fintype.card k ^ r • ellAdicPullback θ.hom (p : ℕ) 1
        (properKummerTateAdicLinearEquiv M p hp y)
    rw [← ht, LinearEquiv.symm_apply_apply]
    have h := properKummerTateAdicEquiv_frobeniusPower k M p hp r θ' g
      (M.functionFieldRingEquiv_semilinear θ' g hfun) hg y
    rw [hθ] at h
    exact h
  have hlin : E.toLinearMap.comp T = Fintype.card k ^ r •
      (ellAdicPullback θ.hom (p : ℕ) 1).comp E.toLinearMap := LinearMap.ext hE
  have hlinQ := congrArg
    (fun f : TateModule (p : ℕ) (G.AlgPoints hc K) →ₗ[ℤ_[p]]
      ellAdicCohomology M.C (p : ℕ) 1 => f.baseChange ℚ_[p]) hlin
  have hsmul := map_nsmul (LinearMap.baseChangeHom ℤ_[p] ℚ_[p]
    (TateModule (p : ℕ) (G.AlgPoints hc K)) (ellAdicCohomology M.C (p : ℕ) 1))
      (Fintype.card k ^ r) ((ellAdicPullback θ.hom (p : ℕ) 1).comp E.toLinearMap)
  change (Fintype.card k ^ r •
      (ellAdicPullback θ.hom (p : ℕ) 1).comp E.toLinearMap).baseChange ℚ_[p] =
    Fintype.card k ^ r •
      ((ellAdicPullback θ.hom (p : ℕ) 1).comp E.toLinearMap).baseChange ℚ_[p] at hsmul
  rw [hsmul, LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hlinQ
  let Eℚ := E.baseChange ℤ_[p] ℚ_[p]
    (TateModule (p : ℕ) (G.AlgPoints hc K)) (ellAdicCohomology M.C (p : ℕ) 1)
  let x := Eℚ.symm v
  have hfixed : T.baseChange ℚ_[p] x = x := by
    apply Eℚ.injective
    have h := LinearMap.congr_fun hlinQ x
    change Eℚ (T.baseChange ℚ_[p] x) =
      Fintype.card k ^ r • rationalEllAdicPullback θ.hom (p : ℕ) 1 (Eℚ x) at h
    rw [show Eℚ x = v from Eℚ.apply_symm_apply v] at h ⊢
    exact h.trans hv.symm
  have hx := rationalTate_eq_zero_of_frobenius_pow_fixed k K D.P D.toBase G hc p r hr x hfixed
  exact (Eℚ.apply_symm_apply v).symm.trans ((congrArg Eℚ hx).trans (map_zero Eℚ))

/-- Inverse arithmetic coefficient twist has no cardinality eigenvector on
the original rational proper H¹. This has geometric Frobenius orientation. -/
theorem properRationalH1_eq_zero_of_inverseTwist_eigenvector
    (v : rationalEllAdicCohomology (p : ℕ) M.C 1)
    (hv : rationalEllAdicPullback θ.inv (p : ℕ) 1 v = Fintype.card k ^ r • v) :
    v = 0 := by
  apply properRationalH1_eq_zero_of_coefficientFrobenius k c ε M eC heC p hp r hr θ
    hproj hbase v
  let ξ := Spec.map (CommRingCat.ofHom
      (algebraMap M.C.functionField (SeparableClosure M.C.functionField))) ≫
    M.C.fromSpecStalk (genericPoint M.C)
  have hi : (rationalEllAdicPullback θ.hom (p : ℕ) 1).comp
      (rationalEllAdicPullback θ.inv (p : ℕ) 1) = LinearMap.id := by
    rw [← rationalEllAdicH1Pullback_comp ξ (p : ℕ), θ.hom_inv_id,
      rationalEllAdicH1Pullback_id ξ (p : ℕ)]
  calc
    v = rationalEllAdicPullback θ.hom (p : ℕ) 1
        (rationalEllAdicPullback θ.inv (p : ℕ) 1 v) :=
      (LinearMap.congr_fun hi v).symm
    _ = Fintype.card k ^ r • rationalEllAdicPullback θ.hom (p : ℕ) 1 v := by
      rw [hv, map_nsmul]

end AnabelianGeometry.FiniteField
