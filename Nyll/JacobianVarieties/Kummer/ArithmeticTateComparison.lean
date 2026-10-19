/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.ArithmeticGenericTate
import Nyll.JacobianVarieties.Kummer.AbelJacobiTate
import Nyll.AlgebraicCurves.Models.Construction.Transport
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.AbelJacobiPicardRepresentability
import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.PicardRepresentabilityBaseChange
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceConjugation
import Nyll.EtaleFundamentalGroups.GeometricFiber.SourceIsoGalois
import Nyll.EtaleFundamentalGroups.GeometricFiber.GeometricAbelianGaloisAction
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedComposition
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
import Mathlib.Algebra.GroupWithZero.Action.Basic

/-!
# Arithmetic equivariance of the existing Abel--Jacobi Tate comparison

The generic identity descends through the actual surjective field-source map.
One fixed base-point correction is removed on the Tate side.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicGeometry.FiniteEtale AlgebraicCurve NeronModelInfra GoodReductionJacobian
open ProCGroups.Abelian

namespace JacobianVarieties.Kummer

attribute [local instance] IsCurveOver.toHasPrincipalDivisors

/-- The existing geometric Tate isomorphism can be chosen equivariantly for
all arithmetic Galois elements, acting on the original Jacobian's points. -/
theorem exists_arithmetic_abelJacobi_fullTate_equiv
    {k K : Type} [Field k] [Field K] [IsAlgClosed K] [CharZero K] [Algebra k K] [IsSepClosure k K]
    {C : Scheme} (c : C ⟶ Spec (.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of k))) c)
    (D : RelativePic0Designation k c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
 :
    let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    let : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated c
    let Y := pullback c (specMap k K)
    let : IsIntegral Y :=
      SmoothProperCurve.isIntegral_pullback_Spec_field k c (specMap k K)
    let s := pullbackSymmetry c (specMap k K)
    let : IsIntegral (pullback (specMap k K) c) := IsIntegral.of_isIso s.hom
    let G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
    let hc : G.IsCommutative :=
      RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut c ε) hD
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra Y.functionField Ω]
      [IsSepClosure Y.functionField Ω],
    let η := Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω))
    let q := Y.fromSpecStalk (genericPoint Y)
    let xi := (η ≫ q) ≫ s.hom
    ∃ E : TopologicalAbelianization (Aut (fiber xi)) ≃ₜ*
        Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)),
      ∀ (σ : K ≃ₐ[k] K) (x : TopologicalAbelianization (Aut (fiber xi))),
        E (geometricAbelianGaloisAction k K C c xi σ x) =
          ProCGroups.FullTateModule.mapHom
            (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) σ.toAlgHom) (E x) := by
  intro hcompact hqs Y hY s hYL G hc Ω hΩ hΩclosed hFΩ hsep η q xi
  classical
  obtain ⟨aj, _, hclass⟩ := exists_abelJacobi_of_representsRelSubPic k c ε D hD
  let : Algebra K Y.functionField :=
    (baseToFunctionField (pullback.snd c (specMap k K))).toAlgebra
  obtain ⟨hcurve, _, M₁, eC, heC, _⟩ :=
    exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
      k c K (specMap k K)
  have : IsCurveOver K Y.functionField := hcurve
  let M : CurveModel K Y.functionField :=
    { M₁.transport (pullback.snd c (specMap k K)) eC heC with
      C := Y
      toBase := baseChange k c K }
  obtain ⟨hbar, hP⟩ := exists_representsRelSubPic_baseChange k c ε D hD K
  let H := RepresentsRelSubPic.relativeGroupLaw
    (P := algEquivZeroGroupCut (baseChange k c K) (sectionBaseChange K ε)) hbar
  let hH : H.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
    (P := algEquivZeroGroupCut (baseChange k c K) (sectionBaseChange K ε)) hbar
  let B := G.algPointsBaseChangeEquiv hc H hH
    (RepresentsRelSubPic.relativeGroupLaw_mul_eq_baseChange_mul_of_nonempty_poincare_iso_ofR
      k c ε D hD K hbar hP)
  let ajK : SchemeHomOver (baseChange k c K) (D.baseChange K).toBase :=
    ⟨pullback.lift (pullback.fst c (specMap k K) ≫ aj.1)
      (pullback.snd c (specMap k K))
      (by rw [Category.assoc, aj.2, pullback.condition]), pullback.lift_snd _ _ _⟩
  obtain ⟨eT, heT⟩ := exists_abelJacobi_fullTate_equiv M (sectionBaseChange K ε)
    (D.baseChange K) hbar ajK
    (abelJacobi_point_class_baseChange k c ε D hD aj hclass K hbar hP) Ω (η ≫ q)
  let epull : FiniteEtale (pullback (specMap k K) c) ≌ FiniteEtale (pullback c (specMap k K)) :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤ s.symm
  let : (FiniteEtale.pullback s.hom).IsEquivalence := epull.isEquivalence_functor
  let eπ := fundamentalGroupEquivOfPullbackEquivalence s.hom (η ≫ q)
  let eab := TopologicalAbelianization.congr eπ
  let E₀ := eab.symm.trans (eT.trans (ProCGroups.FullTateModule.mapEquiv B))
  let jR := fieldSourceAbsoluteGaloisHom Y.functionField Ω q
  let jL := fun ρ : Ω ≃ₐ[Y.functionField] Ω => eπ (jR ρ)
  let μ := fun ρ : Ω ≃ₐ[Y.functionField] Ω =>
    ProCGroups.FullTateModule.mapEquiv B
      (H.fundamentalGroupEquivFullTateAt hH (η ≫ q ≫ ajK.1)
        (fundamentalGroupHom (q ≫ ajK.1) η
          (toAut (fiber η) (Ω ≃ₐ[Y.functionField] Ω) ρ)))
  have hE (ρ : Ω ≃ₐ[Y.functionField] Ω) :
      E₀ (TopologicalAbelianization.mk _ (jL ρ)) = μ ρ := by
    have heab := TopologicalAbelianization.congr_apply_mk eπ (jR ρ)
    change eab (TopologicalAbelianization.mk _ (jR ρ)) =
      TopologicalAbelianization.mk _ (jL ρ) at heab
    change ProCGroups.FullTateModule.mapEquiv B
      (eT (eab.symm (TopologicalAbelianization.mk _ (jL ρ)))) = μ ρ
    rw [← heab, eab.symm_apply_apply, heT]
    apply congrArg (ProCGroups.FullTateModule.mapEquiv B)
    have transport (z z' : Spec (.of Ω) ⟶ (D.baseChange K).P) (h : z = z')
        (a : Aut (fiber z)) :
        H.fundamentalGroupEquivFullTateAt hH z a =
          H.fundamentalGroupEquivFullTateAt hH z' (h ▸ a) := by
      subst z'
      rfl
    have hcomp := fundamentalGroupHom_comp_of_eq q ajK.1 (q ≫ ajK.1) rfl η
      (Category.assoc η q ajK.1)
      (toAut (fiber η) (Ω ≃ₐ[Y.functionField] Ω) ρ)
    exact (transport _ _ (Category.assoc η q ajK.1) _).trans
      (congrArg (H.fundamentalGroupEquivFullTateAt hH (η ≫ q ≫ ajK.1)) hcomp)
  have : Smooth (baseChange k c K) := SmoothOfRelativeDimension.smooth_one _
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral Y := IsNormalIntegral.of_stalks Y
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk (baseChange k c K) z).2)
  let : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (baseChange k c K)
  let : IsDominant q := genericPoint_isDominant Y
  have hjL : Function.Surjective jL :=
    eπ.surjective.comp (fieldSourceAbsoluteGaloisHom_surjective Y.functionField Ω q)
  let p := pullback.snd (specMap k K) c
  let b := pullback.fst (specMap k K) c
  have hsp : s.hom ≫ p = pullback.fst c (specMap k K) := by simp [s, p]
  have hsb : s.hom ≫ b = pullback.snd c (specMap k K) := by simp [s, b]
  let ι : K →+* Ω := (Spec.preimage (xi ≫ b)).hom
  let : Algebra K Ω := ι.toAlgebra
  let : Algebra k Ω := (ι.comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hK : xi ≫ b = ξ K Ω := (Spec.map_preimage (xi ≫ b)).symm
  have hbase : (xi ≫ p) ≫ c = ξ k Ω := by
    calc
      (xi ≫ p) ≫ c = (xi ≫ b) ≫ specMap k K := by
        simp only [p, b, Category.assoc, pullback.condition]
      _ = ξ K Ω ≫ specMap k K := congrArg (fun z => z ≫ specMap k K) hK
      _ = ξ k Ω := by
        change Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k K)) =
            Spec.map (CommRingCat.ofHom (algebraMap k Ω))
        rw [← Spec.map_comp]
        rfl
  obtain ⟨α, hα⟩ := arithmeticFundamentalGroupHom_sourceAction k K Ω c (xi ≫ p) hbase
  have htwist (σ : K ≃ₐ[k] K) (x : TopologicalAbelianization (Aut (fiber xi))) :
      E₀ (geometricAbelianGaloisAction k K C c xi (α * σ * α⁻¹) x) =
        ProCGroups.FullTateModule.mapHom
          (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) σ.toAlgHom) (E₀ x) := by
    obtain ⟨v, rfl⟩ := TopologicalAbelianization.surjective_mk _ x
    obtain ⟨ρ, rfl⟩ := hjL v
    obtain ⟨θ, a, ha, hθproj, hθbase, hsource, hμ⟩ :=
      abelJacobi_generic_fullTate_coefficient_equivariant c ε D hD aj hclass hbar hP Ω σ
    let e := Scheme.Spec.mapIso a.toCommRingCatIso.op
    have hsource' : e.hom ≫ (η ≫ q) = (η ≫ q) ≫ θ.hom := hsource
    have hz : e.hom ≫ (xi ≫ p) = xi ≫ p := by
      calc
        e.hom ≫ (xi ≫ p) = e.hom ≫ ((η ≫ q) ≫ pullback.fst c (specMap k K)) := by
          change e.hom ≫ (((η ≫ q) ≫ s.hom) ≫ p) = _
          rw [Category.assoc (η ≫ q) s.hom p, hsp]
        _ = ((η ≫ q) ≫ θ.hom) ≫ pullback.fst c (specMap k K) := by
          rw [← Category.assoc, hsource']
        _ = (η ≫ q) ≫ pullback.fst c (specMap k K) := by
          rw [Category.assoc, hθproj]
        _ = xi ≫ p := by
          change _ = ((η ≫ q) ≫ s.hom) ≫ p
          rw [Category.assoc (η ≫ q) s.hom p, hsp]
    have hρspec : Spec.map (CommRingCat.ofHom (a.toRingHom.comp (algebraMap K Ω))) =
        Spec.map (CommRingCat.ofHom ((algebraMap K Ω).comp σ.toRingHom)) := by
      change Spec.map (CommRingCat.ofHom (algebraMap K Ω) ≫ CommRingCat.ofHom a.toRingHom) =
        Spec.map (CommRingCat.ofHom σ.toRingHom ≫ CommRingCat.ofHom (algebraMap K Ω))
      rw [Spec.map_comp, Spec.map_comp]
      change e.hom ≫ ξ K Ω = ξ K Ω ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)
      rw [← hK]
      change e.hom ≫ (((η ≫ q) ≫ s.hom) ≫ b) =
        (((η ≫ q) ≫ s.hom) ≫ b) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)
      rw [Category.assoc (η ≫ q) s.hom b, hsb, ← Category.assoc, hsource',
        Category.assoc, hθbase, Category.assoc]
      simp only [Category.assoc]
    have hρ : a.toRingHom.comp (algebraMap K Ω) =
        (algebraMap K Ω).comp σ.toRingHom :=
      congrArg (fun m => m.hom) (Spec.map_injective hρspec)
    let g : Aut (fiber (xi ≫ p)) :=
      fiberSourceIso (xi ≫ p) e ≪≫ eqToIso (congrArg fiber hz)
    have hlabel := hα e a.toRingHom rfl σ hρ hz
    let ρ' := KummerTheory.semilinearGaloisConjugate
      θ.hom.functionFieldRingEquivOfIsOpenImmersion a ha ρ
    have hj (τ : Ω ≃ₐ[Y.functionField] Ω) (Z : FiniteEtale C)
        (z : (fiber (xi ≫ p)).obj Z) :
        (fiberObjEquivHom (xi ≫ p) Z
          ((fundamentalGroupHom p xi (jL τ)).hom.app Z z)).left =
          Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
            (fiberObjEquivHom (xi ≫ p) Z z).left :=
      fundamentalGroupHom_point_of_point_action p xi (jL τ) τ.toRingHom
        (fundamentalGroupHom_point_of_point_action s.hom (η ≫ q) (jR τ) τ.toRingHom
          (fundamentalGroupHom_point_of_point_action q η
            (suppliedGaloisEquivFundamentalGroup Y.functionField Ω τ) τ.toRingHom
            (suppliedGaloisEquivFundamentalGroup_point Y.functionField Ω τ))) Z z
    have hg (Z : FiniteEtale C) (z : (fiber (xi ≫ p)).obj Z) :
        (fiberObjEquivHom (xi ≫ p) Z (g.hom.app Z z)).left =
          Spec.map (CommRingCat.ofHom a.toRingHom) ≫
            (fiberObjEquivHom (xi ≫ p) Z z).left :=
      fiberSourceIso_aut_point (xi ≫ p) e hz Z z
    have hr : ρ'.toRingHom.comp a.toRingHom = a.toRingHom.comp ρ.toRingHom := by
      apply RingHom.ext
      intro z
      change KummerTheory.semilinearGaloisConjugate
        θ.hom.functionFieldRingEquivOfIsOpenImmersion a ha ρ (a z) = a (ρ z)
      rw [KummerTheory.semilinearGaloisConjugate_apply, a.symm_apply_apply]
    have hconj := conjugate_of_point_actions (xi ≫ p)
      (fundamentalGroupHom p xi (jL ρ')) g (fundamentalGroupHom p xi (jL ρ))
      ρ'.toRingHom a.toRingHom ρ.toRingHom (hj ρ') hg (hj ρ) hr
    have hact := geometricAbelianGaloisAction_mk_of_conjugate k K C c xi
      g (jL ρ) (jL ρ') hconj
    rw [hlabel] at hact
    rw [hact, hE, hE]
    exact hμ ρ
  let E := E₀.trans (ProCGroups.FullTateModule.mapEquiv
    (DistribMulAction.toAddEquiv (G.AlgPoints hc K) α))
  refine ⟨E, ?_⟩
  intro τ x
  have ht := htwist (α⁻¹ * τ * α) x
  have hcancel : α * (α⁻¹ * τ * α) * α⁻¹ = τ := by simp [mul_assoc]
  rw [hcancel] at ht
  change ProCGroups.FullTateModule.mapEquiv
      (DistribMulAction.toAddEquiv (G.AlgPoints hc K) α)
      (E₀ (geometricAbelianGaloisAction k K C c xi τ x)) = _
  rw [ht]
  apply Multiplicative.toAdd.injective
  apply ProCGroups.FullTateModule.ext
  intro n
  change α • ((α⁻¹ * τ * α) •
      ProCGroups.FullTateModule.evaluation (G.AlgPoints hc K) n
        (Multiplicative.toAdd (E₀ x))) =
    τ • (α • ProCGroups.FullTateModule.evaluation (G.AlgPoints hc K) n
      (Multiplicative.toAdd (E₀ x)))
  rw [smul_smul, smul_smul]
  congr 1
  simp [mul_assoc]

end JacobianVarieties.Kummer
