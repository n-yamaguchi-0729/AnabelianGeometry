/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ConnectedCoverInertiaIntersection
import Nyll.EtaleFundamentalGroups.Inertia.PlaceNormalizationInertiaRestriction
import Nyll.EtaleFundamentalGroups.Inertia.GenericPlaceInertiaImage

/-!
# Actual inertia intersections for arbitrary connected covers

The prescribed lift determines the cover map and field restriction. The
image of every restricted subgroup is its exact intersection with the
actual cover image.
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

/-- At the same actual localized prime, inertia maps to the exact intersection
with the image of the pointed covering fundamental group. -/
theorem connectedCover_actualPlaceInertia_image
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U]
    (Ω : Type) [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    {k : Type} [Field k] [Algebra k U.functionField]
    (v : Place k U.functionField)
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [Q.IsPrime]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
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
        (genericPlaceInertia W.left (Place.placeOfPrime P) q).map i =
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
    (genericPlaceInertia W.left (Place.placeOfPrime P) q).map i =
      genericPlaceInertia U v Q ⊓ i.range
  have hlocal : q.IsMaximal ∧
      (Q.inertia Gal(Ω/K)).comap r = q.inertia Gal(Ω/L) :=
    placeOfPrime_normalization_inertia_comap v P Q hP
  refine ⟨hlocal.1, ?_⟩
  have hcover : genericPlaceInertia W.left (Place.placeOfPrime P) q =
      ((Q.inertia Gal(Ω/K)).comap r).map qL := by
    rw [genericPlaceInertia_eq_absoluteInertiaImage W.left (Place.placeOfPrime P) q,
      absoluteGenericGaloisToFundamentalGroup_eq_fieldSourceAbsoluteGaloisHom]
    change (q.inertia Gal(Ω/L)).map qL =
      ((Q.inertia Gal(Ω/K)).comap r).map qL
    rw [hlocal.2]
  rw [hcover, genericPlaceInertia_eq_absoluteInertiaImage U v Q]
  exact connectedCover_restrictedSubgroup_image Ω W w (Q.inertia Gal(Ω/K))

end EtaleFundamentalGroups.Inertia
