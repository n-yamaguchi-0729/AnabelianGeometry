/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AnabelianGeometry.WeightFiltration.GenericPlaceInertiaRingEquiv
import Nyll.AnabelianGeometry.WeightFiltration.NamedModelPointedInertia
import Nyll.EtaleFundamentalGroups.Inertia.GenericPlaceInertiaImage
import Nyll.EtaleFundamentalGroups.GeometricFiber.RecoveredCoverGenericPoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
import Nyll.EtaleFundamentalGroups.Inertia.ChosenExtendingInertiaProjection

/-! # Named Square Model Inertia Caller -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicCurve SchemeTheory EtaleFundamentalGroups
open AlgebraicGeometry.FiniteEtale EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] placeBaseAmbientAlgebra placeBaseAmbientTower
  normalizationCommAlgGaloisAction

private theorem namedSquare_pointed_comp_apply
    {Y N U : Scheme} {Ω : Type} [Field Ω]
    (f : Y ⟶ N) (q : N ⟶ U) (w : Y ⟶ U) (hfq : f ≫ q = w)
    (x : Spec (.of Ω) ⟶ Y) (y : Spec (.of Ω) ⟶ N) (z : Spec (.of Ω) ⟶ U)
    (hf : x ≫ f = y) (hq : y ≫ q = z) (hw : x ≫ w = z)
    (a : π₁ᵉᵗ(x)) :
    pointedFundamentalGroupHom q y z hq
        (pointedFundamentalGroupHom f x y hf a) =
      pointedFundamentalGroupHom w x z hw a := by
  subst w
  exact DFunLike.congr_fun (pointedFundamentalGroupHom_comp f q x y z hf hq) a

theorem fieldChart_prescribedPrime_forward_same_inertia
    {k F Ω : Type} [Field k] [Field F] [Algebra k F]
    (X : Scheme) [IsIntegral X]
    [Algebra k X.functionField] [Algebra F X.functionField]
    [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    (e : F ≃ₐ[k] X.functionField)
    (he : ∀ a : F, e a = algebraMap F X.functionField a)
    (p : Place k F)
    (Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω))
    [hQ : Q.IsMaximal] :
    ∃ R : Ideal (normalizationCommAlgCat
        (Place.congrRingEquiv e.toRingEquiv e.commutes p).toValuationSubring Ω),
      R.IsMaximal ∧ genericPlaceInertia X p Q =
        genericPlaceInertia X (Place.congrRingEquiv e.toRingEquiv e.commutes p) R := by
  let r := Place.congrRingEquiv e.toRingEquiv e.commutes p
  let eV : p.toValuationSubring ≃+* r.toValuationSubring :=
    Place.congrValuationSubringEquiv e.toRingEquiv e.commutes p
  let : Algebra p.toValuationSubring r.toValuationSubring := eV.toRingHom.toAlgebra
  let : IsScalarTower p.toValuationSubring r.toValuationSubring Ω := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    calc
      algebraMap p.toValuationSubring Ω a = algebraMap F Ω (a : F) :=
        IsScalarTower.algebraMap_apply p.toValuationSubring F Ω a
      _ = algebraMap X.functionField Ω (algebraMap F X.functionField (a : F)) :=
        IsScalarTower.algebraMap_apply F X.functionField Ω (a : F)
      _ = algebraMap X.functionField Ω (e (a : F)) :=
        congrArg (algebraMap X.functionField Ω) (he (a : F)).symm
      _ = algebraMap r.toValuationSubring Ω (eV a) :=
        (IsScalarTower.algebraMap_apply r.toValuationSubring X.functionField Ω (eV a)).symm
  let : Algebra.IsIntegral p.toValuationSubring r.toValuationSubring := by
    refine ⟨fun b => ?_⟩
    obtain ⟨a, rfl⟩ := eV.surjective b
    exact isIntegral_algebraMap
  let eN : normalizationCommAlgCat r.toValuationSubring Ω ≃+*
      normalizationCommAlgCat p.toValuationSubring Ω :=
    normalizationIntegralBaseRingEquiv p.toValuationSubring r.toValuationSubring Ω
  let R : Ideal (normalizationCommAlgCat r.toValuationSubring Ω) :=
    Q.comap eN.toRingHom
  have hR : R.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective eN.toRingHom eN.surjective (K := Q) (H := hQ)
  refine ⟨R, hR, ?_⟩
  exact genericPlaceInertia_eq_of_valuationRingEquiv X p r eV rfl Q

private theorem namedSquare_same_generic_point
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    (Ω : Type) [Field Ω] [IsSepClosed Ω] [Algebra U.functionField Ω]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W)
    {N : Scheme} [IsIntegral N] (J : W.left ≅ N) :
    let _hWIntegral : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let _AKL : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let lift := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
    let emb := finiteEtaleGenericHomFunctionFieldAlgHom W lift
    let _ALΩ : Algebra W.left.functionField Ω := emb.toRingHom.toAlgebra
    let e := J.hom.functionFieldRingEquivOfIsOpenImmersion
    let _ANΩ : Algebra N.functionField Ω := (emb.toRingHom.comp e.toRingHom).toAlgebra
    W.left.genericExtensionMorphism Ω ≫ J.hom = N.genericExtensionMorphism Ω := by
  intro _hWIntegral _AKL lift emb _ALΩ e _ANΩ
  have hmodel : N.genericExtensionMorphism Ω =
      actualFiberPointLift (U.genericExtensionMorphism Ω) W w ≫ J.hom := by
    exact recoveredCover_genericExtensionMorphism_eq W w J.symm
      (actualFiberPointLift (U.genericExtensionMorphism Ω) W w ≫ J.hom)
      ((Category.assoc _ J.hom J.inv).trans
        ((congrArg (fun z : W.left ⟶ W.left =>
          actualFiberPointLift (U.genericExtensionMorphism Ω) W w ≫ z)
          J.hom_inv_id).trans (Category.comp_id _)))
  have hw := actualFiberPointLift_eq_genericExtension_of_embedding Ω W w
  exact (congrArg (fun z : Spec (.of Ω) ⟶ W.left => z ≫ J.hom) hw).trans hmodel.symm

private theorem namedSquare_prescribedPrime_pointed_image
    {k Ω : Type} [Field k] [Field Ω]
    (X N : Scheme) [IsIntegral X] [IsIntegral N]
    [Algebra k X.functionField] [Algebra k N.functionField]
    [Algebra N.functionField X.functionField]
    [Algebra X.functionField Ω] [Algebra N.functionField Ω]
    [IsScalarTower N.functionField X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure N.functionField Ω]
    (f : X ⟶ N) (e : N.functionField ≃ₐ[k] X.functionField)
    (he : ∀ a : N.functionField, e a = algebraMap N.functionField X.functionField a)
    (p : Place k N.functionField)
    (Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω)) [Q.IsMaximal]
    (hpoint : X.genericExtensionMorphism Ω ≫ f = N.genericExtensionMorphism Ω) :
    ∃ R : Ideal (normalizationCommAlgCat
        (Place.congrRingEquiv e.toRingEquiv e.commutes p).toValuationSubring Ω),
      R.IsMaximal ∧
      (genericPlaceInertia X (Place.congrRingEquiv e.toRingEquiv e.commutes p) R).map
        (pointedFundamentalGroupHom f (X.genericExtensionMorphism Ω)
          (N.genericExtensionMorphism Ω) hpoint).toMonoidHom =
        genericPlaceInertia N p Q := by
  obtain ⟨R, hR, hforward⟩ := fieldChart_prescribedPrime_forward_same_inertia X e he p Q
  refine ⟨R, hR, ?_⟩
  rw [← hforward]
  have hsurj : Function.Surjective (algebraMap N.functionField X.functionField) := by
    intro z
    obtain ⟨a, ha⟩ := e.surjective z
    exact ⟨a, (he a).symm.trans ha⟩
  have h := genericPlaceInertia_pointed_morphism_chart_image X N f p Q
    hsurj (N.fromSpecStalk (genericPoint N)) hpoint
  rw [genericPlaceInertia_eq_absoluteInertiaImage N p Q,
    absoluteGenericGaloisToFundamentalGroup_eq_fieldSourceAbsoluteGaloisHom]
  exact h

private theorem namedSquare_subgroup_image_le
    {G H K : Type*} [Group G] [Group H] [Group K]
    (j : G →* H) (p : H →* K) (i : G →* K)
    (I : Subgroup G) (J : Subgroup H) (T : Subgroup K)
    (himage : I.map j = J) (hcomp : ∀ x, p (j x) = i x)
    (hprojection : I.map i ≤ T) : J.map p ≤ T := by
  rintro z ⟨y, hy, rfl⟩
  have hyCover : y ∈ I.map j := himage.symm ▸ hy
  obtain ⟨x, hx, hxy⟩ := hyCover
  have hxproject : i x ∈ T := hprojection ⟨x, hx, rfl⟩
  have hvalue : p y = i x := (congrArg p hxy.symm).trans (hcomp x)
  exact hvalue.symm ▸ hxproject

private theorem generic_model_inertia_projection
    {k Ω : Type} [Field k] [Field Ω] [IsSepClosed Ω]
    (X N U : Scheme) [IsIntegral X] [IsIntegral N] [IsIntegral U]
    [Algebra k X.functionField] [Algebra k N.functionField]
    [Algebra N.functionField X.functionField]
    [Algebra X.functionField Ω] [Algebra N.functionField Ω]
    [Algebra U.functionField Ω]
    [IsScalarTower N.functionField X.functionField Ω]
    [IsSepClosure X.functionField Ω] [IsSepClosure N.functionField Ω]
    (f : X ⟶ N) (q : N ⟶ U) (w : X ⟶ U) (hfw : f ≫ q = w)
    (e : N.functionField ≃ₐ[k] X.functionField)
    (he : ∀ a : N.functionField, e a = algebraMap N.functionField X.functionField a)
    (p : Place k N.functionField)
    (Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω)) [Q.IsMaximal]
    (hXN : X.genericExtensionMorphism Ω ≫ f = N.genericExtensionMorphism Ω)
    (hXU : X.genericExtensionMorphism Ω ≫ w = U.genericExtensionMorphism Ω)
    (T : Subgroup (π₁ᵉᵗ(U.genericExtensionMorphism Ω)))
    (hprojection : ∀ (R : Ideal (normalizationCommAlgCat
        (Place.congrRingEquiv e.toRingEquiv e.commutes p).toValuationSubring Ω)),
      R.IsMaximal → ∃ a : π₁ᵉᵗ(U.genericExtensionMorphism Ω),
        (genericPlaceInertia X (Place.congrRingEquiv e.toRingEquiv e.commutes p) R).map
          (pointedFundamentalGroupHom w (X.genericExtensionMorphism Ω)
            (U.genericExtensionMorphism Ω) hXU).toMonoidHom ≤
          T.map (MulAut.conj a).toMonoidHom) :
    ∃ hN : N.genericExtensionMorphism Ω ≫ q = U.genericExtensionMorphism Ω,
    ∃ a : π₁ᵉᵗ(U.genericExtensionMorphism Ω),
      (genericPlaceInertia N p Q).map
        (pointedFundamentalGroupHom q (N.genericExtensionMorphism Ω)
          (U.genericExtensionMorphism Ω) hN).toMonoidHom ≤
        T.map (MulAut.conj a).toMonoidHom := by
  obtain ⟨R, hR, hmodel⟩ := namedSquare_prescribedPrime_pointed_image X N f e he p Q hXN
  obtain ⟨a, hprojection⟩ := hprojection R hR
  have hN : N.genericExtensionMorphism Ω ≫ q = U.genericExtensionMorphism Ω :=
    (congrArg (· ≫ q) hXN).symm.trans
      ((Category.assoc _ _ _).trans
        ((congrArg (X.genericExtensionMorphism Ω ≫ ·) hfw).trans hXU))
  let jN := (pointedFundamentalGroupHom f (X.genericExtensionMorphism Ω)
    (N.genericExtensionMorphism Ω) hXN).toMonoidHom
  let pN := (pointedFundamentalGroupHom q (N.genericExtensionMorphism Ω)
    (U.genericExtensionMorphism Ω) hN).toMonoidHom
  let i := (pointedFundamentalGroupHom w (X.genericExtensionMorphism Ω)
    (U.genericExtensionMorphism Ω) hXU).toMonoidHom
  refine ⟨hN, a, ?_⟩
  exact namedSquare_subgroup_image_le jN pN i
    (genericPlaceInertia X (Place.congrRingEquiv e.toRingEquiv e.commutes p) R)
    (genericPlaceInertia N p Q) (T.map (MulAut.conj a).toMonoidHom) hmodel
    (fun x => namedSquare_pointed_comp_apply f q w hfw
      (X.genericExtensionMorphism Ω) (N.genericExtensionMorphism Ω)
      (U.genericExtensionMorphism Ω) hXN hN hXU x) hprojection

theorem namedSquareModel_prescribed_model_inertia_projection
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U]
    (Ω : Type) [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    {k : Type} [Field k] [Algebra k U.functionField]
    (v : Place k U.functionField)
    (Qbase : Ideal (integralClosure v.toValuationSubring Ω)) [Qbase.IsMaximal]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W)
    {N : Scheme} [IsIntegral N] (J : W.left ≅ N)
    (qN : N ⟶ U) (hJq : J.hom ≫ qN = W.hom) :
    let _hWIntegral : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let K := U.functionField
    let L := W.left.functionField
    let _AKL : Algebra K L := finiteEtaleFunctionFieldAlgebra W
    let _hKLfinite : FiniteDimensional K L :=
      finiteDimensional_functionField_of_finiteEtale_isConnected W
    let hKLsep : Algebra.IsSeparable K L :=
      isSeparable_functionField_of_finiteEtale_isConnected W
    let lift := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
    let emb := finiteEtaleGenericHomFunctionFieldAlgHom W lift
    let _ALΩ : Algebra L Ω := emb.toRingHom.toAlgebra
    let hKLΩ : IsScalarTower K L Ω := by
      apply IsScalarTower.of_algebraMap_eq'
      ext z
      exact (emb.commutes z).symm
    let _hSepL : IsSepClosure L Ω :=
      ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
    let AkL : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
    let hkKL : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
    let e := J.hom.functionFieldRingEquivOfIsOpenImmersion
    let ANL : Algebra N.functionField L := e.toRingHom.toAlgebra
    let _ANΩ : Algebra N.functionField Ω := (emb.toRingHom.comp e.toRingHom).toAlgebra
    let _hNLΩ : IsScalarTower N.functionField L Ω := IsScalarTower.of_algebraMap_eq' rfl
    ∀ (A : Algebra k N.functionField),
      let modelConstants : Algebra k N.functionField := A
      ∀ (he : ∀ a : k, e (algebraMap k N.functionField a) = algebraMap k L a),
      let eAlg : N.functionField ≃ₐ[k] L := { e with commutes' := he }
      ∀ (hsep : IsSepClosure N.functionField Ω),
      let modelSeparableClosure : IsSepClosure N.functionField Ω := hsep
      ∀ (p : Place k N.functionField)
        (Qmodel : Ideal (normalizationCommAlgCat p.toValuationSubring Ω)),
      Qmodel.IsMaximal →
      (Place.congrRingEquiv eAlg.toRingEquiv eAlg.commutes p).restrict K = v →
      ∃ hN : N.genericExtensionMorphism Ω ≫ qN = U.genericExtensionMorphism Ω,
      ∃ a : π₁ᵉᵗ(U.genericExtensionMorphism Ω),
        (genericPlaceInertia N p Qmodel).map
          (pointedFundamentalGroupHom qN (N.genericExtensionMorphism Ω)
            (U.genericExtensionMorphism Ω) hN).toMonoidHom ≤
          (genericPlaceInertia U v Qbase).map (MulAut.conj a).toMonoidHom := by
  intro _hWIntegral K L _AKL hKLfinite hKLsep lift emb _ALΩ hKLΩ hSepL AkL hkKL
    e ANL _ANΩ hNLΩ A modelConstants he eAlg hsep modelSeparableClosure
    p Qmodel hQmodel hr
  have : Qmodel.IsMaximal := hQmodel
  have hJN : W.left.genericExtensionMorphism Ω ≫ J.hom = N.genericExtensionMorphism Ω :=
    namedSquare_same_generic_point Ω W w J
  have hW : W.left.genericExtensionMorphism Ω ≫ W.hom = U.genericExtensionMorphism Ω :=
    finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W lift
  exact generic_model_inertia_projection W.left N U J.hom qN W.hom hJq
    eAlg (fun _ => rfl) p Qmodel hJN hW (genericPlaceInertia U v Qbase)
    (fun R hR => connectedCover_chosenExtendingPlaceInertia_projection Ω v Qbase W w
      (Place.congrRingEquiv eAlg.toRingEquiv eAlg.commutes p) hr R hR)

end AnabelianGeometry.WeightFiltration
