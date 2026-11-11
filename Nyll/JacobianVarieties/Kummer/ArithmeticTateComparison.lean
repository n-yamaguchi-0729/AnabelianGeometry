/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.JacobianVarieties.Kummer.ArithmeticGenericTate
public import Nyll.JacobianVarieties.Kummer.AbelJacobiTate
public import Nyll.AlgebraicCurves.Models.Construction.Transport
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.AbelJacobiPicardRepresentability
public import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.PicardRepresentabilityBaseChange
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceConjugation
public import Nyll.EtaleFundamentalGroups.GeometricFiber.SourceIsoGalois
public import Nyll.EtaleFundamentalGroups.GeometricFiber.GeometricAbelianGaloisAction
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedComposition
public import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualEquivalence
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericPointCharacterDetection
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldMonodromyLift
public import Mathlib.Algebra.GroupWithZero.Action.Basic
public import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
public import Nyll.ProCGroups.Abelian.FullTateModule
public import Nyll.ProCGroups.Abelian.FullTateModuleMap
public import Nyll.ProCGroups.Abelian.RestrictedTateModule
public import Nyll.ProCGroups.Abelian.RestrictedTateTransport
public import Nyll.ProCGroups.FiniteGroups.StandardClasses
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualCore

/-!
# Arithmetic equivariance of the existing Abel--Jacobi Tate comparison

The generic identity descends through the actual surjective field-source map.
One fixed base-point correction is removed on the Tate side.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicGeometry.FiniteEtale AlgebraicCurve NeronModelInfra GoodReductionJacobian
open ProCGroups.Abelian

namespace JacobianVarieties.Kummer

attribute [local instance] IsCurveOver.toHasPrincipalDivisors

/-- Pointed composition can be evaluated in any family on the actual target
fundamental groups, using the prescribed equality of geometric points. -/
private theorem fundamentalGroupHom_comp_apply
    {X Y Z : Scheme.{u}} {Ω : Type u} [Field Ω]
    (f : X ⟶ Y) (g : Y ⟶ Z) (point : Spec (.of Ω) ⟶ X)
    {T : Type v} (F : ∀ z : Spec (.of Ω) ⟶ Z, Aut (fiber z) → T)
    (a : Aut (fiber point)) :
    F ((point ≫ f) ≫ g)
        (fundamentalGroupHom g (point ≫ f) (fundamentalGroupHom f point a)) =
      F (point ≫ f ≫ g) (fundamentalGroupHom (f ≫ g) point a) := by
  have transport (z z' : Spec (.of Ω) ⟶ Z) (h : z = z') (b : Aut (fiber z)) :
      F z b = F z' (h ▸ b) := by
    subst z'
    rfl
  have hcomp := fundamentalGroupHom_comp_of_eq f g (f ≫ g) rfl point
    (Category.assoc point f g) a
  exact (transport _ _ (Category.assoc point f g) _).trans
    (congrArg (F (point ≫ f ≫ g)) hcomp)

/-- The inverse of the actual residual-quotient equivalence retains
representatives. The supplied equivalence is used directly, including
when its source and target are already abelianizations. -/
private theorem sigmaResidualCongr_symm_apply_mk
    {A B : Type u} [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalGroup A] [IsTopologicalGroup B]
    [CompactSpace A] [CompactSpace B] [T2Space A] [T2Space B]
    (Sigma : Set ℕ) (e : A ≃ₜ* B) (x : A) :
    let NS := ProCGroups.ProC.proCResidualCore (ProCGroups.FiniteGroupClass.sigmaGroup Sigma) A
    let NT := ProCGroups.ProC.proCResidualCore (ProCGroups.FiniteGroupClass.sigmaGroup Sigma) B
    let eSigma : (A ⧸ NS) ≃ₜ* (B ⧸ NT) :=
      ProCGroups.ProC.residualQuotientContinuousMulEquiv
        (ProCGroups.FiniteGroupClass.sigmaGroup_fullFormation Sigma).hereditary e
    eSigma.symm (QuotientGroup.mk' NT (e x)) = QuotientGroup.mk' NS x := by
  intro NS NT eSigma
  have hforward : eSigma (QuotientGroup.mk' NS x) = QuotientGroup.mk' NT (e x) :=
    ProCGroups.ProC.residualQuotientContinuousMulEquiv_apply_mk
      (ProCGroups.FiniteGroupClass.sigmaGroup_fullFormation Sigma).hereditary e x
  exact (congrArg eSigma.symm hforward).symm.trans (eSigma.symm_apply_apply _)

/-- The actual source action fixes the first projection, and its second
projection identifies the induced coefficient ring homomorphism. -/
private theorem sourceAction_projection_computations
    (k K Ω : Type u) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω]
    {Y C : Scheme.{u}} (point : Spec (.of Ω) ⟶ Y)
    (p : Y ⟶ C) (b : Y ⟶ Spec (.of K))
    (θ : Y ≅ Y) (a : Ω ≃+* Ω) (σ : K ≃ₐ[k] K)
    (hsource : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ point = point ≫ θ.hom)
    (hproj : θ.hom ≫ p = p)
    (hbase : θ.hom ≫ b = b ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
    (hK : point ≫ b = ξ K Ω) :
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (point ≫ p) = point ≫ p ∧
      a.toRingHom.comp (algebraMap K Ω) =
        (algebraMap K Ω).comp σ.toRingHom := by
  constructor
  · rw [← Category.assoc, hsource, Category.assoc, hproj]
  · have hspec : Spec.map (CommRingCat.ofHom (a.toRingHom.comp (algebraMap K Ω))) =
        Spec.map (CommRingCat.ofHom ((algebraMap K Ω).comp σ.toRingHom)) := by
      change Spec.map (CommRingCat.ofHom (algebraMap K Ω) ≫ CommRingCat.ofHom a.toRingHom) =
        Spec.map (CommRingCat.ofHom σ.toRingHom ≫ CommRingCat.ofHom (algebraMap K Ω))
      rw [Spec.map_comp, Spec.map_comp]
      rw [← hK, ← Category.assoc, hsource, Category.assoc, hbase, Category.assoc]
    exact congrArg (fun m => m.hom) (Spec.map_injective hspec)

/-- The existing geometric Tate isomorphism can be chosen equivariantly for
all arithmetic Galois elements, acting on the original Jacobian's points. -/
theorem exists_arithmetic_abelJacobi_fullTate_equiv
    {k K : Type u} [Field k] [Field K] [IsAlgClosed K] [CharZero K] [Algebra k K] [IsSepClosure k K]
    {C : Scheme.{u}} (c : C ⟶ Spec (.of k))
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
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra Y.functionField Ω]
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
    exact fundamentalGroupHom_comp_apply q ajK.1 η
      (fun z a => H.fundamentalGroupEquivFullTateAt hH z a)
      (toAut (fiber η) (Ω ≃ₐ[Y.functionField] Ω) ρ)
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
  have hsp : s.hom ≫ p = pullback.fst c (specMap k K) := by
    exact pullbackSymmetry_hom_comp_snd c (specMap k K)
  have hsb : s.hom ≫ b = pullback.snd c (specMap k K) := by
    exact pullbackSymmetry_hom_comp_fst c (specMap k K)
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
      Aut.of (fiberSourceIso (xi ≫ p) e ≪≫ eqToIso (congrArg fiber hz))
    have hlabel := hα e a.toRingHom rfl σ hρ hz
    let ρ' := KummerTheory.semilinearGaloisConjugate
      θ.hom.functionFieldRingEquivOfIsOpenImmersion a ha ρ
    have hj (τ : Ω ≃ₐ[Y.functionField] Ω) (Z : FiniteEtale C)
        (z : (fiber (xi ≫ p)).obj Z) :
        (fiberObjEquivHom (xi ≫ p) Z
          ((fundamentalGroupHom p xi (jL τ)).asIso.hom.app Z z)).left =
          Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
            (fiberObjEquivHom (xi ≫ p) Z z).left :=
      fundamentalGroupHom_point_of_point_action p xi (jL τ) τ.toRingHom
        (fundamentalGroupHom_point_of_point_action s.hom (η ≫ q) (jR τ) τ.toRingHom
          (fundamentalGroupHom_point_of_point_action q η
            (suppliedGaloisEquivFundamentalGroup Y.functionField Ω τ) τ.toRingHom
            (suppliedGaloisEquivFundamentalGroup_point Y.functionField Ω τ))) Z z
    have hg (Z : FiniteEtale C) (z : (fiber (xi ≫ p)).obj Z) :
        (fiberObjEquivHom (xi ≫ p) Z (g.asIso.hom.app Z z)).left =
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
  have hcancel : α * (α⁻¹ * τ * α) * α⁻¹ = τ := by
    simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
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
  simp only [← mul_assoc, mul_inv_cancel, one_mul]

/-- The geometric pro-Sigma Tate isomorphism can be chosen equivariantly for
all arithmetic Galois elements, acting on the original Jacobian's points. -/
theorem exists_arithmetic_abelJacobi_sigmaTate_equiv
    {k K : Type u} [Field k] [Field K] [IsAlgClosed K] [Algebra k K] [IsSepClosure k K]
    {C : Scheme.{u}} (c : C ⟶ Spec (.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of k))) c)
    (D : RelativePic0Designation k c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (Sigma : Set ℕ)
    (hI : ∀ n : ProCGroups.sigmaTorsionIndices Sigma, IsUnit ((n.val : ℕ) : K)) :
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
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra Y.functionField Ω]
      [IsAlgClosure Y.functionField Ω],
    let η := Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω))
    let q := Y.fromSpecStalk (genericPoint Y)
    let xi := (η ≫ q) ≫ s.hom
    ∃ E :
        (TopologicalAbelianization (Aut (fiber xi)) ⧸
          ProCGroups.ProC.proCResidualCore (ProCGroups.FiniteGroupClass.sigmaGroup Sigma)
            (TopologicalAbelianization (Aut (fiber xi)))) ≃ₜ*
        Multiplicative (ProCGroups.RestrictedTateModule (G.AlgPoints hc K)
          (ProCGroups.sigmaTorsionIndices Sigma)),
      ∀ (σ : K ≃ₐ[k] K)
        (x : TopologicalAbelianization (Aut (fiber xi)) ⧸
          ProCGroups.ProC.proCResidualCore (ProCGroups.FiniteGroupClass.sigmaGroup Sigma)
            (TopologicalAbelianization (Aut (fiber xi)))),
        E (geometricSigmaAbelianGaloisAction k K C c xi Sigma σ x) =
          ProCGroups.RestrictedTateModule.mapHom
            (M := G.AlgPoints hc K) (N := G.AlgPoints hc K)
            (S := ProCGroups.sigmaTorsionIndices Sigma)
            (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) σ.toAlgHom) (E x) := by
  intro hcompact hqs Y hY s hYL G hc Ω hΩ hΩclosed hFΩ hsep η q xi
  classical
  have hAJExists := exists_abelJacobi_of_representsRelSubPic k c ε D hD
  obtain ⟨aj, _, hclass⟩ := hAJExists
  let : Algebra K Y.functionField :=
    (baseToFunctionField (pullback.snd c (specMap k K))).toAlgebra
  have hModelExists :=
    exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
      k c K (specMap k K)
  obtain ⟨hcurve, _, M₁, eC, heC, _⟩ := hModelExists
  have : IsCurveOver K Y.functionField := hcurve
  let M : CurveModel K Y.functionField :=
    { M₁.transport (pullback.snd c (specMap k K)) eC heC with
      C := Y
      toBase := baseChange k c K }
  have hBaseExists := exists_representsRelSubPic_baseChange k c ε D hD K
  obtain ⟨hbar, hP⟩ := hBaseExists
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
  have hTateExists := exists_abelJacobi_sigmaTate_equiv M (sectionBaseChange K ε)
    (D.baseChange K) hbar ajK
    (abelJacobi_point_class_baseChange k c ε D hD aj hclass K hbar hP) Sigma hI Ω (η ≫ q)
  obtain ⟨eT, heT⟩ := hTateExists
  let epull : FiniteEtale (pullback (specMap k K) c) ≌ FiniteEtale (pullback c (specMap k K)) :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤ s.symm
  let : (FiniteEtale.pullback s.hom).IsEquivalence := epull.isEquivalence_functor
  let eπ := fundamentalGroupEquivOfPullbackEquivalence s.hom (η ≫ q)
  let eab := TopologicalAbelianization.congr eπ
  let NS := ProCGroups.ProC.proCResidualCore (ProCGroups.FiniteGroupClass.sigmaGroup Sigma)
    (TopologicalAbelianization (Aut (fiber (η ≫ q))))
  let NT := ProCGroups.ProC.proCResidualCore (ProCGroups.FiniteGroupClass.sigmaGroup Sigma)
    (TopologicalAbelianization (Aut (fiber xi)))
  let eSigma :
      (TopologicalAbelianization (Aut (fiber (η ≫ q))) ⧸ NS) ≃ₜ*
        (TopologicalAbelianization (Aut (fiber xi)) ⧸ NT) :=
    ProCGroups.ProC.residualQuotientContinuousMulEquiv
    (ProCGroups.FiniteGroupClass.sigmaGroup_fullFormation Sigma).hereditary eab
  let E₀ : (TopologicalAbelianization (Aut (fiber xi)) ⧸ NT) ≃ₜ*
      Multiplicative (ProCGroups.RestrictedTateModule (G.AlgPoints hc K)
        (ProCGroups.sigmaTorsionIndices Sigma)) :=
    eSigma.symm.trans (eT.trans (ProCGroups.RestrictedTateModule.mapEquiv B))
  let jR : (Ω ≃ₐ[Y.functionField] Ω) → Aut (fiber (η ≫ q)) := fun ρ =>
    fundamentalGroupHom q η (toAut (fiber η) (Ω ≃ₐ[Y.functionField] Ω) ρ)
  let jL : (Ω ≃ₐ[Y.functionField] Ω) → Aut (fiber xi) := fun ρ => eπ (jR ρ)
  let μ : (Ω ≃ₐ[Y.functionField] Ω) →
      Multiplicative (ProCGroups.RestrictedTateModule (G.AlgPoints hc K)
        (ProCGroups.sigmaTorsionIndices Sigma)) := fun ρ =>
    ProCGroups.RestrictedTateModule.mapEquiv B
      (RelativeGroupLaw.UnitMultiplication.fundamentalGroupSigmaEquivTateAt
        H hH Sigma hI (η ≫ q ≫ ajK.1)
        (QuotientGroup.mk'
          (ProCGroups.ProC.proCResidualCore (ProCGroups.FiniteGroupClass.sigmaGroup Sigma)
            (Aut (fiber (η ≫ q ≫ ajK.1))))
          (fundamentalGroupHom (q ≫ ajK.1) η
            (toAut (fiber η) (Ω ≃ₐ[Y.functionField] Ω) ρ))))
  have hE (ρ : Ω ≃ₐ[Y.functionField] Ω) :
      E₀ (QuotientGroup.mk' NT (TopologicalAbelianization.mk _ (jL ρ))) = μ ρ := by
    have heab : eab (TopologicalAbelianization.mk _ (jR ρ)) =
        TopologicalAbelianization.mk _ (jL ρ) :=
      TopologicalAbelianization.congr_apply_mk eπ (jR ρ)
    have hpreimage : eSigma.symm
        (QuotientGroup.mk' NT (TopologicalAbelianization.mk _ (jL ρ))) =
        QuotientGroup.mk' NS (TopologicalAbelianization.mk _ (jR ρ)) :=
      (congrArg (fun z => eSigma.symm (QuotientGroup.mk' NT z)) heab).symm.trans
        (sigmaResidualCongr_symm_apply_mk Sigma eab (TopologicalAbelianization.mk _ (jR ρ)))
    have hT := (congrArg eT hpreimage).trans (heT (jR ρ))
    change ProCGroups.RestrictedTateModule.mapEquiv B
      (eT (eSigma.symm
        (QuotientGroup.mk' NT (TopologicalAbelianization.mk _ (jL ρ))))) = μ ρ
    refine (congrArg (ProCGroups.RestrictedTateModule.mapEquiv B) hT).trans ?_
    apply congrArg (ProCGroups.RestrictedTateModule.mapEquiv B)
    exact fundamentalGroupHom_comp_apply q ajK.1 η
      (fun z a => RelativeGroupLaw.UnitMultiplication.fundamentalGroupSigmaEquivTateAt
        H hH Sigma hI z
        (QuotientGroup.mk'
          (ProCGroups.ProC.proCResidualCore (ProCGroups.FiniteGroupClass.sigmaGroup Sigma)
            (Aut (fiber z))) a))
      (toAut (fiber η) (Ω ≃ₐ[Y.functionField] Ω) ρ)
  have : Smooth (baseChange k c K) := SmoothOfRelativeDimension.smooth_one _
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral Y := IsNormalIntegral.of_stalks Y
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk (baseChange k c K) z).2)
  let : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (baseChange k c K)
  let : IsDominant q := genericPoint_isDominant Y
  have hjL : Function.Surjective jL :=
    eπ.surjective.comp (genericFieldAction_surjective Y Ω)
  let p := pullback.snd (specMap k K) c
  let b := pullback.fst (specMap k K) c
  have hsp : s.hom ≫ p = pullback.fst c (specMap k K) := by
    exact pullbackSymmetry_hom_comp_snd c (specMap k K)
  have hsb : s.hom ≫ b = pullback.snd c (specMap k K) := by
    exact pullbackSymmetry_hom_comp_fst c (specMap k K)
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
  have hcorrection :=
    arithmeticFundamentalGroupHom_sourceAction k K Ω c (xi ≫ p) hbase
  obtain ⟨α, hα⟩ := hcorrection
  have htwist (σ : K ≃ₐ[k] K) :
      ∀ (x : TopologicalAbelianization (Aut (fiber xi)) ⧸ NT),
      E₀ (geometricSigmaAbelianGaloisAction k K C c xi Sigma (α * σ * α⁻¹) x) =
        ProCGroups.RestrictedTateModule.mapHom
          (M := G.AlgPoints hc K) (N := G.AlgPoints hc K)
          (S := ProCGroups.sigmaTorsionIndices Sigma)
          (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) σ.toAlgHom) (E₀ x) := by
    have hcoefficient := abelJacobi_generic_sigmaTate_coefficient_equivariant
      c ε D hD aj hclass hbar hP Sigma hI Ω σ
    obtain ⟨θ, a, ha, hθproj, hθbase, hsource, hμ⟩ := hcoefficient
    let e := Scheme.Spec.mapIso a.toCommRingCatIso.op
    have hsource' : e.hom ≫ (η ≫ q) = (η ≫ q) ≫ θ.hom := hsource
    have hpR : xi ≫ p = (η ≫ q) ≫ pullback.fst c (specMap k K) := by
      change ((η ≫ q) ≫ s.hom) ≫ p = _
      rw [Category.assoc (η ≫ q) s.hom p, hsp]
    have hbR : (η ≫ q) ≫ pullback.snd c (specMap k K) = ξ K Ω := by
      calc
        _ = xi ≫ b := by
          change _ = ((η ≫ q) ≫ s.hom) ≫ b
          rw [Category.assoc (η ≫ q) s.hom b, hsb]
        _ = ξ K Ω := hK
    have hSourceProjections := sourceAction_projection_computations k K Ω (η ≫ q)
      (pullback.fst c (specMap k K)) (pullback.snd c (specMap k K))
      θ a σ hsource' hθproj hθbase hbR
    obtain ⟨hzR, hρ⟩ := hSourceProjections
    have hz : e.hom ≫ (xi ≫ p) = xi ≫ p := by
      rw [hpR]
      exact hzR
    let g : Aut (fiber (xi ≫ p)) :=
      Aut.of (fiberSourceIso (xi ≫ p) e ≪≫ eqToIso (congrArg fiber hz))
    have hlabel := hα e a.toRingHom rfl σ hρ hz
    intro x
    have hquotientExists := QuotientGroup.mk'_surjective NT x
    obtain ⟨z, hquotientRepresentative⟩ := hquotientExists
    cases hquotientRepresentative
    have habelianExists :=
      TopologicalAbelianization.surjective_mk (Aut (fiber xi)) z
    obtain ⟨v, habelianRepresentative⟩ := habelianExists
    cases habelianRepresentative
    have hfieldExists := hjL v
    obtain ⟨ρ, hfieldRepresentative⟩ := hfieldExists
    cases hfieldRepresentative
    let ρ' : Ω ≃ₐ[Y.functionField] Ω :=
      KummerTheory.semilinearGaloisConjugate (K := Y.functionField) (Ω := Ω)
        θ.hom.functionFieldRingEquivOfIsOpenImmersion a ha ρ
    have hj (τ : Ω ≃ₐ[Y.functionField] Ω) (Z : FiniteEtale C)
        (z : (fiber (xi ≫ p)).obj Z) :
        (fiberObjEquivHom (xi ≫ p) Z
          ((fundamentalGroupHom p xi (jL τ)).asIso.hom.app Z z)).left =
          Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
            (fiberObjEquivHom (xi ≫ p) Z z).left :=
      fundamentalGroupHom_point_of_point_action p xi (jL τ) τ.toRingHom
        (fundamentalGroupHom_point_of_point_action s.hom (η ≫ q) (jR τ) τ.toRingHom
          (fun W w => fundamentalGroupHom_field_fiberLift q W τ w)) Z z
    have hg (Z : FiniteEtale C) (z : (fiber (xi ≫ p)).obj Z) :
        (fiberObjEquivHom (xi ≫ p) Z (g.asIso.hom.app Z z)).left =
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
    dsimp only [g] at hact
    rw [hlabel] at hact
    have hdescend := geometricSigmaAbelianGaloisAction_mk k K C c xi Sigma
      (α * σ * α⁻¹) (TopologicalAbelianization.mk _ (jL ρ))
    have hquotient := hdescend.trans (congrArg (QuotientGroup.mk' NT) hact)
    have hcompare := (congrArg E₀ hquotient).trans (hE ρ')
    exact hcompare.trans ((hμ ρ).trans (congrArg
      (ProCGroups.RestrictedTateModule.mapHom
        (M := G.AlgPoints hc K) (N := G.AlgPoints hc K)
        (S := ProCGroups.sigmaTorsionIndices Sigma)
        (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) σ.toAlgHom))
      (hE ρ).symm))
  let E := E₀.trans (ProCGroups.RestrictedTateModule.mapEquiv
    (DistribMulAction.toAddEquiv (G.AlgPoints hc K) α))
  refine ⟨E, ?_⟩
  intro τ x
  have ht := htwist (α⁻¹ * τ * α) x
  have hcancel : α * (α⁻¹ * τ * α) * α⁻¹ = τ := by
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  rw [hcancel] at ht
  change ProCGroups.RestrictedTateModule.mapEquiv
      (DistribMulAction.toAddEquiv (G.AlgPoints hc K) α)
      (E₀ (geometricSigmaAbelianGaloisAction k K C c xi Sigma τ x)) = _
  rw [ht]
  apply Multiplicative.toAdd.injective
  apply ProCGroups.RestrictedTateModule.ext
  intro n
  change α • ((α⁻¹ * τ * α) •
      ProCGroups.RestrictedTateModule.evaluation (G.AlgPoints hc K)
      (ProCGroups.sigmaTorsionIndices Sigma) n
        (Multiplicative.toAdd (E₀ x))) =
    τ • (α • ProCGroups.RestrictedTateModule.evaluation (G.AlgPoints hc K)
      (ProCGroups.sigmaTorsionIndices Sigma) n
      (Multiplicative.toAdd (E₀ x)))
  rw [smul_smul, smul_smul]
  congr 1
  simp only [mul_assoc, mul_inv_cancel_left]

end JacobianVarieties.Kummer
