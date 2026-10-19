/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.SemilinearGenericTate
import Nyll.ProCGroups.Abelian.FullTateModuleMap
import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicPointsEquivariance
import Nyll.JacobianVarieties.Picard.AbelJacobi.AbelJacobiPointClassBaseChange
import Nyll.JacobianVarieties.Picard.GroupLaw.PicardRepresentabilityRelativeGroupLawMulEqBaseChangeMul
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPointsBaseChange
import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearFunctionField
import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
import Nyll.AnabelianGeometry.WeightFiltration.GenericSourceIso

/-!
# The original arithmetic coefficient action on the generic Tate comparison

The geometric point group is identified by its actual pullback projection
with the points of the original Jacobian. One equivariant Picard comparison
is used at every torsion level.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Kummer

attribute [local instance] IsCurveOver.toHasPrincipalDivisors

/-- The inverse point comparison is determined by the two actual pullback projections. -/
private theorem inverseBaseChangePoint_eq
    {𝒞 : Type*} [Category 𝒞] {S T A X : 𝒞}
    (f : A ⟶ S) (s : T ⟶ S) [HasPullback f s]
    {U V : Type*} [AddCommGroup U] [AddCommGroup V]
    (B : U ≃+ V)
    (p : U → (T ⟶ pullback f s)) (q : V → (T ⟶ A))
    (hp : ∀ u, p u ≫ pullback.snd f s = 𝟙 T)
    (hB : ∀ u, q (B u) = p u ≫ pullback.fst f s)
    (x : V) (t : T ⟶ X) (j : X ⟶ pullback f s) (l : X ⟶ A)
    (ht : (t ≫ j) ≫ pullback.snd f s = 𝟙 T)
    (hj : j ≫ pullback.fst f s = l) (hx : q x = t ≫ l) :
    p (B.symm x) = t ≫ j := by
  apply pullback.hom_ext
  · exact (hB (B.symm x)).symm.trans
      ((congrArg q (B.apply_symm_apply x)).trans
        (hx.trans ((Category.assoc t j (pullback.fst f s)).trans
          (congrArg (t ≫ ·) hj)).symm))
  · exact (hp _).trans ht.symm

/-- Intertwining additive maps transports their action on the existing full Tate module. -/
private theorem fullTateMapEquivariant
    {P U V : Type*} [AddCommGroup P] [AddCommGroup U] [AddCommGroup V]
    (e : P ≃+ V) (B : U ≃+ V) (g : P →+ P) (s : V →+ V)
    (he : ∀ z : P, e (g z) = s (e z))
    (x y : Multiplicative (ProCGroups.FullTateModule U))
    (hxy : x = Multiplicative.ofAdd (ProCGroups.FullTateModule.map
      ((e.trans B.symm).toAddMonoidHom.comp
        (g.comp (e.trans B.symm).symm.toAddMonoidHom)) (Multiplicative.toAdd y))) :
    ProCGroups.FullTateModule.mapEquiv B x =
      ProCGroups.FullTateModule.mapHom s (ProCGroups.FullTateModule.mapEquiv B y) := by
  let e₀ : P ≃+ U := e.trans B.symm
  let f : U →+ U :=
    e₀.toAddMonoidHom.comp (g.comp e₀.symm.toAddMonoidHom)
  have hmap : B.toAddMonoidHom.comp f = s.comp B.toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro z
    change B (e₀ (g (e₀.symm z))) = s (B z)
    calc
      B (e₀ (g (e₀.symm z))) = e (g (e₀.symm z)) := B.apply_symm_apply _
      _ = s (e (e₀.symm z)) := he _
      _ = s (B z) := congrArg s
        ((B.apply_symm_apply (e (e₀.symm z))).symm.trans
          (congrArg B (e₀.apply_symm_apply z)))
  have htB := congrArg (ProCGroups.FullTateModule.mapEquiv B) hxy
  apply htB.trans
  apply Multiplicative.toAdd.injective
  change ProCGroups.FullTateModule.map B.toAddMonoidHom
      (ProCGroups.FullTateModule.map f (Multiplicative.toAdd y)) =
    ProCGroups.FullTateModule.map s
      (ProCGroups.FullTateModule.map B.toAddMonoidHom (Multiplicative.toAdd y))
  rw [← ProCGroups.FullTateModule.map_comp, hmap, ProCGroups.FullTateModule.map_comp]

/-- Transport the existing generic Tate comparison through one specified
additive equivalence, retaining its supplied Picard point comparison. -/
private theorem transported_generic_fullTate_semilinear
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
    ∀ {V : Type} [AddCommGroup V] (B : G.AlgPoints hc K ≃+ V) (e : Pic0 K F₀ ≃+ V),
      (∀ v : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase,
        ∃ Dv : Divisor.degZero (K := K) (F := F₀),
          (Dv : Divisor K F₀) = Finsupp.single (M₀.pointEquivPlace v) 1 -
            Finsupp.single (M₀.pointEquivPlace ε) 1 ∧
          (RelativeGroupLaw.AlgPoints.toPoint (B.symm (e (Pic0.mk Dv)))).1 =
            v.1 ≫ aj.1) →
    ∀ (g : SemilinearAut K F₀) (φ : M₀.C.functionField ≃+* M₀.C.functionField)
      (_hφ : ∀ r : F₀, φ (M₀.ffEquiv r) = M₀.ffEquiv (SemilinearAut.toRingAut g r))
      (a : Ω ≃+* Ω)
      (ha : ∀ r : M₀.C.functionField,
        a (algebraMap M₀.C.functionField Ω r) = algebraMap M₀.C.functionField Ω (φ r))
      (σ : Ω ≃ₐ[M₀.C.functionField] Ω) (s : V →+ V)
      (_he : ∀ z : Pic0 K F₀, e (g • z) = s (e z)),
      let μ := fun ρ : Ω ≃ₐ[M₀.C.functionField] Ω =>
        G.fundamentalGroupEquivFullTateAt hc (η ≫ q ≫ aj.1)
          (FiniteEtale.fundamentalGroupHom (q ≫ aj.1) η
            (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M₀.C.functionField] Ω) ρ))
      ProCGroups.FullTateModule.mapEquiv B
          (μ (KummerTheory.semilinearGaloisConjugate φ a ha σ)) =
        ProCGroups.FullTateModule.mapHom s (ProCGroups.FullTateModule.mapEquiv B (μ σ)) := by
  intro G hc η q V hV B e hpoint g φ hφ a ha σ s he μ
  exact fullTateMapEquivariant e B
    (DistribSMul.toAddMonoidHom (Pic0 K F₀) g) s he
    (μ (KummerTheory.semilinearGaloisConjugate φ a ha σ)) (μ σ)
    (actual_abelJacobi_generic_fullTate_semilinear M₀ hbase ε D hD aj hclass
      (e.trans B.symm) hpoint g φ hφ a ha σ)

/-- The generic full Tate comparison intertwines semilinear conjugation with
literal coefficient automorphisms of the original arithmetic Jacobian. -/
theorem abelJacobi_generic_fullTate_coefficient_equivariant
    {k K : Type} [Field k] [Field K] [IsAlgClosed K] [CharZero K] [Algebra k K]
    {C : Scheme} (c : C ⟶ Spec (.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of k))) c)
    (D : RelativePic0Designation k c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (aj : SchemeHomOver c D.toBase)
    (hclass : ∀ (L : Type) [Field L] (t : Spec (.of L) ⟶ Spec (.of k))
      (x : SchemeHomOver t c),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (hbar : RepresentsRelSubPic (baseChange k c K) (sectionBaseChange K ε)
      (algEquivZeroCut (baseChange k c K) (sectionBaseChange K ε)) (D.baseChange K))
    (hP : Nonempty (hbar.poincare.L ≅ (BaseChange.ofR c ε K
      (hD.poincare.pullbackAlong
        ⟨pullback.fst D.toBase (specMap k K), pullback.condition⟩)).L)) :
    let Y := pullback c (specMap k K)
    let : IsIntegral Y :=
      SmoothProperCurve.isIntegral_pullback_Spec_field k c (specMap k K)
    let G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
    let hc : G.IsCommutative :=
      RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut c ε) hD
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
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra Y.functionField Ω]
      [IsSepClosure Y.functionField Ω],
    let η := Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω))
    let q := Y.fromSpecStalk (genericPoint Y)
    let μ := fun ρ : Ω ≃ₐ[Y.functionField] Ω =>
      ProCGroups.FullTateModule.mapEquiv B
        (H.fundamentalGroupEquivFullTateAt hH (η ≫ q ≫ ajK.1)
          (FiniteEtale.fundamentalGroupHom (q ≫ ajK.1) η
            (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[Y.functionField] Ω) ρ)))
    ∀ σ : K ≃ₐ[k] K,
    ∃ (θ : Y ≅ Y) (a : Ω ≃+* Ω)
      (ha : ∀ r : Y.functionField, a (algebraMap Y.functionField Ω r) =
        algebraMap Y.functionField Ω (θ.hom.functionFieldRingEquivOfIsOpenImmersion r)),
      θ.hom ≫ pullback.fst c (specMap k K) = pullback.fst c (specMap k K) ∧
      θ.hom ≫ pullback.snd c (specMap k K) =
        pullback.snd c (specMap k K) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ∧
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (η ≫ q) = (η ≫ q) ≫ θ.hom ∧
      ∀ ρ : Ω ≃ₐ[Y.functionField] Ω,
        μ (KummerTheory.semilinearGaloisConjugate
          θ.hom.functionFieldRingEquivOfIsOpenImmersion a ha ρ) =
        ProCGroups.FullTateModule.mapHom
          (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) σ.toAlgHom) (μ ρ) := by
  intro Y hY G hc H hH B ajK Ω hΩ hΩclosed hEΩ hsep η q μ
  classical
  let : Algebra K Y.functionField :=
    (baseToFunctionField (pullback.snd c (specMap k K))).toAlgebra
  let : Algebra K Ω := ((algebraMap Y.functionField Ω).comp
    (algebraMap K Y.functionField)).toAlgebra
  have : IsScalarTower K Y.functionField Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsCurveOver K Y.functionField :=
    (literalCurveModel_functionField_properties (baseChange k c K)).1
  let M₁ : CurveModel K Y.functionField :=
    literalCurveModel (baseChange k c K)
  let M : CurveModel K Y.functionField :=
    { C := Y
      toBase := baseChange k c K
      isIntegral := hY
      isProper := inferInstance
      smooth := inferInstance
      ffEquiv := RingEquiv.refl Y.functionField
      ffEquiv_algebraMap := fun _ => rfl
      placeOfPoint := M₁.placeOfPoint
      placeOfPoint_bijective := M₁.placeOfPoint_bijective
      range_stalk_eq := M₁.range_stalk_eq
      finset_subset_affineOpen := M₁.finset_subset_affineOpen }
  have : GeometricallyIntegral M.toBase :=
    inferInstanceAs (GeometricallyIntegral (baseChange k c K))
  obtain ⟨e, hepoint, heaction⟩ :=
    JacobianVarieties.Picard.exists_pic0_algPoints_equivariant_of_abelJacobi
      c ε D hD aj hclass M (Iso.refl Y) (Category.id_comp _)
  have hid : (Iso.refl Y).hom ≫ pullback.fst c (specMap k K) =
      pullback.fst c (specMap k K) := CategoryTheory.Category.id_comp _
  have hidaj : (Iso.refl Y).hom ≫ pullback.fst c (specMap k K) ≫ aj.1 =
      pullback.fst c (specMap k K) ≫ aj.1 := CategoryTheory.Category.id_comp _
  have hpoint : ∀ v : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase,
      ∃ Dv : Divisor.degZero (K := K) (F := Y.functionField),
        (Dv : Divisor K Y.functionField) = Finsupp.single (M.pointEquivPlace v) 1 -
          Finsupp.single (M.pointEquivPlace (sectionBaseChange K ε)) 1 ∧
        (RelativeGroupLaw.AlgPoints.toPoint (L := H) (hc := hH) (T := K)
          (B.symm (e (Pic0.mk Dv)))).1 = v.1 ≫ ajK.1 := by
    intro v
    obtain ⟨Dv, hDv, hval⟩ := hepoint v (sectionBaseChange K ε)
      ((congrArg (fun t : Y ⟶ C => (sectionBaseChange K ε).val ≫ t) hid).trans
        (sectionBaseChange_coe_fst K ε))
    refine ⟨Dv, hDv, ?_⟩
    exact inverseBaseChangePoint_eq D.toBase (specMap k K) B
      (fun x => (RelativeGroupLaw.AlgPoints.toPoint
        (L := H) (hc := hH) (T := K) x).val)
      (fun x => (RelativeGroupLaw.AlgPoints.toPoint
        (L := G) (hc := hc) (T := K) x).val)
      (fun x => (RelativeGroupLaw.AlgPoints.toPoint
        (L := H) (hc := hH) (T := K) x).property.trans
          (by rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]))
      (fun x => G.algPointsBaseChangeEquiv_toPoint hc H hH
        (RepresentsRelSubPic.relativeGroupLaw_mul_eq_baseChange_mul_of_nonempty_poincare_iso_ofR
          k c ε D hD K hbar hP) x)
      (e (Pic0.mk Dv)) v.val ajK.val (pullback.fst c (specMap k K) ≫ aj.val)
      ((Category.assoc v.val ajK.val _).trans
        ((congrArg (v.val ≫ ·) ajK.property).trans v.property))
      (pullback.lift_fst _ _ _)
      (hval.trans (congrArg (fun t : Y ⟶ D.P => (v.val : Spec (.of K) ⟶ Y) ≫ t) hidaj))
  intro σ
  obtain ⟨θ, g, hθproj, hθbase, _, hgfun, _, hge⟩ := heaction σ
  obtain ⟨a, ha, hsource⟩ :=
    AnabelianGeometry.WeightFiltration.exists_genericPoint_sourceIso (X := Y) (show Y ≅ Y from θ) Ω
  refine ⟨θ, a, ha, ?_, hθbase, hsource, ?_⟩
  · exact (congrArg (fun t : Y ⟶ C => (θ.hom : Y ⟶ Y) ≫ t) hid).symm.trans
      (hθproj.trans hid)
  intro ρ
  have hφ := M.functionFieldRingEquiv_semilinear θ g hgfun
  exact @transported_generic_fullTate_semilinear
    K Y.functionField _ _ _ _ _ _ M
    (inferInstance : Algebra K Y.functionField) rfl
    Ω hΩ hΩclosed (inferInstance : Algebra K Ω)
    hEΩ (inferInstance : IsScalarTower K Y.functionField Ω) inferInstance hsep
    (inferInstance : IsProper (baseChange k c K))
    (inferInstance : SmoothOfRelativeDimension 1 (baseChange k c K))
    (inferInstance : GeometricallyIntegral (baseChange k c K))
    (sectionBaseChange K ε) (D.baseChange K) hbar
    inferInstance inferInstance inferInstance ajK
    (abelJacobi_point_class_baseChange k c ε D hD aj hclass K hbar hP)
    _ _ B e hpoint g θ.hom.functionFieldRingEquivOfIsOpenImmersion hφ a ha ρ
    (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) σ.toAlgHom)
    (fun z => hge z)

end JacobianVarieties.Kummer
