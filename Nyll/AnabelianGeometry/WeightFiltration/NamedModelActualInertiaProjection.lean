/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Inertia.ConnectedCoverActualInertia
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps

/-! # The same localized inertia projects through its actual named model

The named-model projection equation is supplied by the existing model
construction; no comparison between source and target configurations is assumed.
The original w fixes the ambient algebra, original contracted prime P and
localized prime q. The theorem maps that very subgroup through J, without
replacing it by a fresh rational boundary prime.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
namespace EtaleFundamentalGroups.Inertia
universe u
open AlgebraicCurve IsDedekindDomain
open AnabelianGeometry.WeightFiltration
attribute [local instance]
  Place.instIsFractionRingIntegralClosureAt
  Place.instIsDedekindDomainIntegralClosureAt
  Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  placeBaseAmbientAlgebra placeBaseAmbientTower
  extendingPlaceAmbientAlgebra extendingPlaceAmbientTower
  finiteNormalizationPlaceAlgebra finiteNormalizationPlaceTower
  finiteNormalizationPlaceLocalization finiteNormalizationPlaceAmbientTower
  originalPlaceNormalizationAction extendingPlaceNormalizationAction

/-- Exact projection image, hence containment via `inf_le_left`, including at
ramified boundary points. No surjectivity onto the downstairs inertia is used. -/
theorem connectedCover_namedModel_actualPlaceInertia_projection
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U]
    (Ω : Type) [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    {k : Type} [Field k] [Algebra k U.functionField]
    (v : Place k U.functionField)
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [Q.IsPrime]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W)
    {N : Scheme} (J : W.left ≅ N) (qN : N ⟶ U)
    (hJ : J.hom ≫ qN = W.hom) :
    letI : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let K := U.functionField
    let L := W.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra W
    letI : FiniteDimensional K L :=
      finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : Algebra.IsSeparable K L :=
      isSeparable_functionField_of_finiteEtale_isConnected W
    let g := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
    let j := finiteEtaleGenericHomFunctionFieldAlgHom W g
    letI : Algebra L Ω := j.toRingHom.toAlgebra
    letI : IsScalarTower K L Ω := by
      apply IsScalarTower.of_algebraMap_eq'
      ext z
      exact (j.commutes z).symm
    letI : IsSepClosure L Ω :=
      ⟨IsSepClosure.sep_closed K,
        Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
    let jL := W.left.fromSpecStalk (genericPoint W.left)
    let hpoint : (ξ L Ω ≫ jL) ≫ W.hom = U.genericExtensionMorphism Ω :=
      finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W g
    let i := (pointedFundamentalGroupHom W.hom (ξ L Ω ≫ jL)
      (U.genericExtensionMorphism Ω) hpoint).toMonoidHom
    let yN := (ξ L Ω ≫ jL) ≫ J.hom
    let hN : yN ≫ qN = U.genericExtensionMorphism Ω := by
      rw [Category.assoc, hJ, hpoint]
    let jN := (pointedFundamentalGroupHom J.hom (ξ L Ω ≫ jL) yN rfl).toMonoidHom
    let pN := (pointedFundamentalGroupHom qN yN
      (U.genericExtensionMorphism Ω) hN).toMonoidHom
    letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
    letI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
    ∀ (P : HeightOneSpectrum (Place.integralClosureAt L v)),
      P.asIdeal = absoluteNormalizationPrimeContraction
        (A := v.toValuationSubring) (L := L) (Omega := Ω) Q →
      let R := (Place.placeOfPrime P).toValuationSubring
      let QB := Q.comap (normalizationIntegralBaseRingEquiv
        v.toValuationSubring (Place.integralClosureAt L v) Ω).toRingHom
      let q := QB.map
        (normalizationBaseLocalizationRingMap (Place.integralClosureAt L v) R Ω)
      q.IsMaximal ∧
        ((genericPlaceInertia W.left (Place.placeOfPrime P) q).map jN).map pN =
          genericPlaceInertia U v Q ⊓ i.range := by
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let K := U.functionField
  let L := W.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra W
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : Algebra.IsSeparable K L :=
    isSeparable_functionField_of_finiteEtale_isConnected W
  let g := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
  let j := finiteEtaleGenericHomFunctionFieldAlgHom W g
  let : Algebra L Ω := j.toRingHom.toAlgebra
  let : IsScalarTower K L Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    ext z
    exact (j.commutes z).symm
  let : IsSepClosure L Ω :=
    ⟨IsSepClosure.sep_closed K,
      Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
  let jL := W.left.fromSpecStalk (genericPoint W.left)
  let hpoint : (ξ L Ω ≫ jL) ≫ W.hom = U.genericExtensionMorphism Ω :=
    finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W g
  let i := (pointedFundamentalGroupHom W.hom (ξ L Ω ≫ jL)
    (U.genericExtensionMorphism Ω) hpoint).toMonoidHom
  let yN := (ξ L Ω ≫ jL) ≫ J.hom
  let hN : yN ≫ qN = U.genericExtensionMorphism Ω := by
    rw [Category.assoc, hJ, hpoint]
  let jN := (pointedFundamentalGroupHom J.hom (ξ L Ω ≫ jL) yN rfl).toMonoidHom
  let pN := (pointedFundamentalGroupHom qN yN
    (U.genericExtensionMorphism Ω) hN).toMonoidHom
  let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  change ∀ (P : HeightOneSpectrum (Place.integralClosureAt L v)),
    P.asIdeal = absoluteNormalizationPrimeContraction
      (A := v.toValuationSubring) (L := L) (Omega := Ω) Q → _
  intro P hP
  let R := (Place.placeOfPrime P).toValuationSubring
  let QB := Q.comap (normalizationIntegralBaseRingEquiv
    v.toValuationSubring (Place.integralClosureAt L v) Ω).toRingHom
  let q := QB.map
    (normalizationBaseLocalizationRingMap (Place.integralClosureAt L v) R Ω)
  let qL := (fieldSourceAbsoluteGaloisHom L Ω jL).toMonoidHom
  let r : Gal(Ω/L) →* Gal(Ω/K) := AlgEquiv.restrictScalarsHom K
  change q.IsMaximal ∧
    ((genericPlaceInertia W.left (Place.placeOfPrime P) q).map jN).map pN =
      genericPlaceInertia U v Q ⊓ i.range
  obtain ⟨hq, himage⟩ := connectedCover_actualPlaceInertia_image Ω v Q W w P hP
  refine ⟨hq, ?_⟩
  have hcomp : pN.comp jN = i := by
    apply MonoidHom.ext
    intro z
    change pointedFundamentalGroupHom qN yN (U.genericExtensionMorphism Ω) hN
        (pointedFundamentalGroupHom J.hom (ξ L Ω ≫ jL) yN rfl z) =
      pointedFundamentalGroupHom W.hom (ξ L Ω ≫ jL)
        (U.genericExtensionMorphism Ω) hpoint z
    have h := pointedFundamentalGroupHom_comp J.hom qN
      (ξ L Ω ≫ jL) yN (U.genericExtensionMorphism Ω) rfl hN
    have hz := DFunLike.congr_fun h z
    change pointedFundamentalGroupHom qN yN (U.genericExtensionMorphism Ω) hN
        (pointedFundamentalGroupHom J.hom (ξ L Ω ≫ jL) yN rfl z) =
      pointedFundamentalGroupHom (J.hom ≫ qN) (ξ L Ω ≫ jL)
        (U.genericExtensionMorphism Ω) _ z at hz
    simpa only [hJ] using hz
  rw [Subgroup.map_map, hcomp]
  exact himage

end EtaleFundamentalGroups.Inertia
