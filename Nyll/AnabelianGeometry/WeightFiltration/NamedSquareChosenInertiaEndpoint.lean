/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareModelInertiaCaller
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareCoherentBaseChangeCaller
import Nyll.AlgebraicCurves.Places.Restriction.PlaceChartRestrictionSquare
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalConfigurationCuspRecognition
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineAmbientFields
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineFunctionFields
import Nyll.AlgebraicCurves.Models.Ramification.BoundaryNormalizationPrimes
import Nyll.EtaleFundamentalGroups.GeometricFiber.RecoveredCoverGenericPoint
import Nyll.AnabelianGeometry.WeightFiltration.NamedModelPointedInertia

/-! # Chosen inertia at the endpoint of a named square

The existing field square and geometric cover comparison transport the chosen
normalization-prime inertia to its corresponding base place.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups EtaleFundamentalGroups.Inertia SchemeTheory
open CategoryTheory.PreGaloisCategory
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower
  placeBaseAmbientAlgebra placeBaseAmbientTower normalizationCommAlgGaloisAction
namespace AnabelianGeometry.WeightFiltration

local instance chosenSquareSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

/-- The chosen inertia groups on the cover model project into conjugates of the inertia groups
at the corresponding restricted places on the base. -/
def namedSquareChosenInertiaProjection
    (E κ : Type) [Field E] [Field κ] [CharZero κ] [Algebra E κ] [Infinite E]
    (t : Finset (Projectivization E (E × E)))
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U]
    (cU : RatFunc κ ≃+* U.functionField)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [IsSepClosed Ω]
    [Algebra U.functionField Ω] [@IsAlgClosure U.functionField Ω _ _ _
      DivisionSemiring.to_moduleIsTorsionFree]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W)
    (J : W.left ≅ rationalConfigurationGeometricScheme E κ t)
    (qN : rationalConfigurationGeometricScheme E κ t ⟶ U)
    (eκ : RatFunc κ ≃ₐ[κ] RatFunc κ) : Prop :=
    let N := rationalConfigurationGeometricScheme E κ t
    let K := U.functionField
    let _AκK : Algebra κ K := (cU.toRingHom.comp (algebraMap κ (RatFunc κ))).toAlgebra
    let _hcharK : CharZero K := Algebra.charZero_of_charZero (R := κ) (A := K)
    let _hSepK : IsSepClosure K Ω := inferInstance
    let _hWIntegral : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let L := W.left.functionField
    let _AKL : Algebra K L := finiteEtaleFunctionFieldAlgebra W
    let lift := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
    let emb := finiteEtaleGenericHomFunctionFieldAlgHom W lift
    let eR := J.hom.functionFieldRingEquivOfIsOpenImmersion
    let _ANΩ : Algebra N.functionField Ω := (emb.toRingHom.comp eR.toRingHom).toAlgebra
    ∃ hclosure : @IsAlgClosure N.functionField Ω _ _ _
      DivisionSemiring.to_moduleIsTorsionFree,
    let _modelClosure : @IsAlgClosure N.functionField Ω _ _ _
      DivisionSemiring.to_moduleIsTorsionFree := hclosure
    ∃ hN : N.genericExtensionMorphism Ω ≫ qN = U.genericExtensionMorphism Ω,
    ∀ (p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart E κ t))
      (v : Place κ (RatFunc κ)),
      p.val.restrictAlong (AnabelianGeometry.KummerTheory.ratFuncPairSquareHom eκ)
        (AnabelianGeometry.KummerTheory.ratFuncPairSquareHom_isIntegral eκ) = v →
      let eU : RatFunc κ ≃ₐ[κ] K := { cU with commutes' := fun _ => rfl }
      let vU := Place.congrRingEquiv eU.toRingEquiv eU.commutes v
      ∀ (Qbase : Ideal (integralClosure vU.toValuationSubring Ω)), Qbase.IsMaximal →
      ∃ a : π₁ᵉᵗ(U.genericExtensionMorphism Ω),
        (rationalConfigurationChosenInertia E κ t Ω p).map
          (pointedFundamentalGroupHom qN (N.genericExtensionMorphism Ω)
            (U.genericExtensionMorphism Ω) hN).toMonoidHom ≤
          (genericPlaceInertia U vU Qbase).map (MulAut.conj a).toMonoidHom

theorem namedSquareChosenInertiaProjection_of_fieldSquare
    (E κ : Type) [Field E] [Field κ] [CharZero κ] [Algebra E κ] [Infinite E]
    (t : Finset (Projectivization E (E × E)))
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U]
    (cU : RatFunc κ ≃+* U.functionField)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [IsSepClosed Ω]
    [Algebra U.functionField Ω] [@IsAlgClosure U.functionField Ω _ _ _
      DivisionSemiring.to_moduleIsTorsionFree]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W)
    (J : W.left ≅ rationalConfigurationGeometricScheme E κ t)
    (qN : rationalConfigurationGeometricScheme E κ t ⟶ U)
    (eκ : RatFunc κ ≃ₐ[κ] RatFunc κ)
    (hJq : J.hom ≫ qN = W.hom)
    (hsquare :
      let _hWIntegral : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
      let _AKL : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
      ∀ z : RatFunc κ,
        J.hom.functionFieldMap J.hom.homeomorph.surjective.denseRange
          (rationalConfigurationGeometricFunctionFieldEquiv E κ t
            (AnabelianGeometry.KummerTheory.ratFuncPairSquareHom eκ z)) =
          algebraMap U.functionField W.left.functionField (cU z)) :
    namedSquareChosenInertiaProjection E κ t cU Ω W w J qN eκ := by
  unfold namedSquareChosenInertiaProjection
  intro N K AκK hcharK hSepK hWIntegral L AKL lift emb eR ANΩ
  let : FiniteDimensional K L := finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : Algebra.IsSeparable K L := isSeparable_functionField_of_finiteEtale_isConnected W
  let : Algebra L Ω := emb.toRingHom.toAlgebra
  let : IsScalarTower K L Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    ext z
    exact (emb.commutes z).symm
  let : IsSepClosure L Ω :=
    ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
  let : Algebra κ L := ((algebraMap K L).comp (algebraMap κ K)).toAlgebra
  let : IsScalarTower κ K L := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra N.functionField L := eR.toRingHom.toAlgebra
  let : IsScalarTower N.functionField L Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := K) (A := Ω) L
  let : IsAlgClosure L Ω := ⟨inferInstance, inferInstance⟩
  let : Algebra.IsAlgebraic N.functionField L := by
    refine ⟨fun z => ?_⟩
    obtain ⟨x, rfl⟩ := eR.surjective z
    apply IsIntegral.isAlgebraic
    exact isIntegral_algebraMap
  have hclosure : @IsAlgClosure N.functionField Ω _ _ _
      DivisionSemiring.to_moduleIsTorsionFree :=
    IsAlgClosure.ofAlgebraic N.functionField L Ω
  let : CharZero N.functionField := Algebra.charZero_of_charZero (R := κ) (A := N.functionField)
  have hsep : IsSepClosure N.functionField Ω := inferInstance
  let eU : RatFunc κ ≃ₐ[κ] K := { cU with commutes' := fun _ => rfl }
  let eC := rationalConfigurationGeometricFieldAlgEquiv E κ t
  have heR (a : κ) : eR (algebraMap κ N.functionField a) = algebraMap κ L a := by
    change eR (rationalConfigurationGeometricFunctionFieldEquiv E κ t
      (algebraMap κ (RatFunc κ) a)) =
      algebraMap K L (cU (algebraMap κ (RatFunc κ) a))
    have h := hsquare (algebraMap κ (RatFunc κ) a)
    rw [(AnabelianGeometry.KummerTheory.ratFuncPairSquareHom eκ).commutes a] at h
    exact h
  let eRAlg : N.functionField ≃ₐ[κ] L := { eR with commutes' := heR }
  let eL := eC.trans eRAlg
  have hfield (z : RatFunc κ) :
      eL (AnabelianGeometry.KummerTheory.ratFuncPairSquareHom eκ z) =
        algebraMap K L (eU z) := hsquare z
  have hmodel : N.genericExtensionMorphism Ω =
      actualFiberPointLift (U.genericExtensionMorphism Ω) W w ≫ J.hom := by
    exact recoveredCover_genericExtensionMorphism_eq W w J.symm
      (actualFiberPointLift (U.genericExtensionMorphism Ω) W w ≫ J.hom)
      ((Category.assoc _ J.hom J.inv).trans
        ((congrArg (fun z : W.left ⟶ W.left =>
          actualFiberPointLift (U.genericExtensionMorphism Ω) W w ≫ z)
          J.hom_inv_id).trans (Category.comp_id _)))
  have hJN : W.left.genericExtensionMorphism Ω ≫ J.hom = N.genericExtensionMorphism Ω := by
    have hw := actualFiberPointLift_eq_genericExtension_of_embedding Ω W w
    exact (congrArg (fun z : Spec (.of Ω) ⟶ W.left => z ≫ J.hom) hw).trans hmodel.symm
  have hW : W.left.genericExtensionMorphism Ω ≫ W.hom = U.genericExtensionMorphism Ω :=
    finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W lift
  have hN : N.genericExtensionMorphism Ω ≫ qN = U.genericExtensionMorphism Ω := by
    rw [← hJN, Category.assoc, hJq, hW]
  change ∃ hclosure : @IsAlgClosure N.functionField Ω _ _ _
      DivisionSemiring.to_moduleIsTorsionFree, _
  refine ⟨hclosure, ?_⟩
  intro modelClosure
  refine ⟨hN, ?_⟩
  intro p v hrestrict
  let vU := Place.congrRingEquiv eU.toRingEquiv eU.commutes v
  change ∀ (Qbase : Ideal (integralClosure vU.toValuationSubring Ω)), _
  intro Qbase hQbase
  let : Qbase.IsMaximal := hQbase
  have hactual := Place.congrRingEquiv_restrict_eq_of_fieldSquare eU eL
    (AnabelianGeometry.KummerTheory.ratFuncPairSquareHom eκ)
    (AnabelianGeometry.KummerTheory.ratFuncPairSquareHom_isIntegral eκ)
    hfield p.val v hrestrict
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra E κ t Ω
  let : IsScalarTower (RatFunc κ) N.functionField Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : IsAlgClosure (RatFunc κ) Ω := rationalConfigurationAmbient_isAlgClosure_geometric E κ t Ω
  let : IsSepClosure (RatFunc κ) Ω := inferInstance
  let Qmodel := (projectiveLineRatFuncModel κ).boundaryNormalizationPrimes
    (Ω := Ω) (rationalConfigurationBaseChangeChart E κ t) p
  have hQmodel : Qmodel.IsMaximal :=
    (projectiveLineRatFuncModel κ).boundaryNormalizationPrimes_isMaximal
      (Ω := Ω) (rationalConfigurationBaseChangeChart E κ t) p
  let pN := Place.congrRingEquiv eC.toRingEquiv eC.commutes p.val
  obtain ⟨R, hR, hforward⟩ :=
    fieldChart_prescribedPrime_forward_same_inertia N eC (fun _ => rfl) p.val Qmodel
      (hQ := hQmodel)
  have hcompPlace : Place.congrRingEquiv eRAlg.toRingEquiv eRAlg.commutes pN =
      Place.congrRingEquiv eL.toRingEquiv eL.commutes p.val := by
    apply Place.ext
    ext z
    rfl
  have hr : (Place.congrRingEquiv eRAlg.toRingEquiv eRAlg.commutes pN).restrict K = vU := by
    rw [hcompPlace]
    exact hactual
  obtain ⟨hN', a, hprojection⟩ :=
    namedSquareModel_prescribed_model_inertia_projection Ω vU Qbase W w J qN hJq
      (rationalConfigurationGeometricConstantAlgebra E κ t) heR hsep pN R hR hr
  refine ⟨a, ?_⟩
  rw [← hforward] at hprojection
  exact hprojection

local instance chosenEndpointBaseChangeOverCategory (S : Scheme) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme) ⊤ S) :=
  AlgebraicGeometry.FiniteEtale.instCategory S
local instance chosenEndpointBaseChangeHasPullbacksAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun _ _ ↦ inferInstance⟩
local instance chosenEndpointBaseChangeStableUnderBaseChangeAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme)) h hf⟩

theorem namedSquareModel_actual_chosen_inertia_endpoint
    (E κ : Type) [Field E] [Field κ] [Algebra E κ] [Infinite E] [CharZero κ]
    {X : Scheme} (j : X ⟶ (projectiveLineRatFuncModel E).C) [IsOpenImmersion j]
    (W : FiniteEtale X)
    (eE : RatFunc E ≃ₐ[E] RatFunc E) (eκ : RatFunc κ ≃ₐ[κ] RatFunc κ)
    (u : RatFunc E) (heE : eE RatFunc.X = u)
    (heκ : eκ RatFunc.X = algebraMap (RatFunc E) (RatFunc κ) u)
    (p : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
    (hp : p ≫ π E 1 = π E 1)
    (hpGeneric : (projectiveLineRatFuncModel E).C.fromSpecStalk
        (genericPoint (projectiveLineRatFuncModel E).C) ≫ p =
      Spec.map (CommRingCat.ofHom ((projectiveLineRatFuncModel E).ffEquiv.toRingHom.comp
        ((AnabelianGeometry.KummerTheory.ratFuncPairSquareHom eE).toRingHom.comp
          (projectiveLineRatFuncModel E).ffEquiv.symm.toRingHom))) ≫
            (projectiveLineRatFuncModel E).C.fromSpecStalk
              (genericPoint (projectiveLineRatFuncModel E).C))
    (t : Finset (Projectivization E (E × E)))
    (J : W.left ≅ (rationalConfigurationOpen t : Scheme))
    (q : (rationalConfigurationOpen t : Scheme) ⟶ X)
    (hJq : J.hom ≫ q = W.hom)
    (hq : q ≫ j = (rationalConfigurationOpen t).ι ≫ p)
    [IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) (j ≫ π E 1))]
    [IsNormalIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) (j ≫ π E 1))]
    [IsLocallyNoetherian (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) (j ≫ π E 1))]
    [IsConnected ((FiniteEtale.pullback
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) (j ≫ π E 1))).obj W)]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [IsSepClosed Ω]
    [Algebra (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (j ≫ π E 1)).functionField Ω]
    [IsAlgClosure (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (j ≫ π E 1)).functionField Ω] :
    let φ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
    let f := j ≫ π E 1
    let g := (rationalConfigurationOpen t).ι ≫ π E 1
    let b := pullback.snd φ f
    let Uκ := pullback φ f
    let Wκ := (FiniteEtale.pullback b).obj W
    let ξκ := Uκ.genericExtensionMorphism Ω
    let jκ : Uκ ⟶ (projectiveLineRatFuncModel κ).C :=
      (isPullback_map E κ 1).flip.lift (pullback.fst φ f)
        (b ≫ j) (by
          exact (pullback.condition (f := φ) (g := f)).trans
            (Category.assoc b j
              (show (projectiveLineRatFuncModel E).C ⟶ Spec (.of E) from π E 1)).symm)
    ∃ Jκ : Wκ.left ≅ rationalConfigurationGeometricScheme E κ t,
      Jκ.hom ≫ pullback.snd φ g = pullback.fst W.hom b ≫ J.hom ∧
      Jκ.hom ≫ pullback.fst φ g = Wκ.hom ≫ pullback.fst φ f ∧
      ∃ hjκ : IsOpenImmersion jκ,
      let geometricOpenImmersion : IsOpenImmersion jκ := hjκ
      ∀ w : (fiber (ξκ ≫ b)).obj W,
        let wκ := (pointedPullbackFiberEquiv b ξκ (ξκ ≫ b) rfl W).symm w
        namedSquareChosenInertiaProjection E κ t
          ((projectiveLineRatFuncModel κ).ffEquiv.trans
            jκ.functionFieldRingEquivOfIsOpenImmersion)
          Ω Wκ wκ Jκ (Jκ.inv ≫ Wκ.hom) eκ := by
  intro φ f g b Uκ Wκ ξκ jκ
  obtain ⟨Jκ, hcoeff, hbase, _hqcoeff, _hqbase, hopen, hfield, _hpoint⟩ :=
    namedSquareModel_coherent_actualBaseChange E κ j W eE eκ u heE heκ
      p hp hpGeneric t J q hJq hq Ω
  refine ⟨Jκ, hcoeff, hbase, hopen, ?_⟩
  intro geometricOpenImmersion w
  let wκ := (pointedPullbackFiberEquiv b ξκ (ξκ ≫ b) rfl W).symm w
  exact namedSquareChosenInertiaProjection_of_fieldSquare E κ t
    ((projectiveLineRatFuncModel κ).ffEquiv.trans
      jκ.functionFieldRingEquivOfIsOpenImmersion)
    Ω Wκ wκ Jκ (Jκ.inv ≫ Wκ.hom) eκ
    (Jκ.hom_inv_id_assoc Wκ.hom) hfield

end AnabelianGeometry.WeightFiltration
