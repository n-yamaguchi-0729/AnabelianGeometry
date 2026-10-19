/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ConnectedCoverActualInertia
import Nyll.EtaleFundamentalGroups.Inertia.AbsolutePrimeContractionOrbit
import Nyll.EtaleFundamentalGroups.Inertia.InertiaConjugateImage
import Nyll.EtaleFundamentalGroups.Inertia.PlaceNormalizationInertiaRestriction
import Nyll.EtaleFundamentalGroups.Inertia.GenericPlaceInertiaImage

/-! # Every actual extending place with its original localized prime

This exports the nonabelian prime-orbit step used internally by
ConnectedCoverCuspRanges. Given any actual extending place r, it obtains r
from a translate of the ORIGINAL downstairs prime Q and retains the exact
localized upstairs prime. There is no choice of a replacement cover or w.
The input restriction equality is supplied for named rational labels by the
constructed model's actual field map; it is not a coordinate comparison
between the two configurations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

open AlgebraicCurve IsDedekindDomain
open scoped Pointwise
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

/-- Every actual extending place has a localized inertia whose image is
exactly a conjugate of the original base inertia intersected with the actual
cover-group image. The conjugator is the image of the retained prime translate. -/
theorem connectedCover_actualExtendingPlaceInertia_image
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U]
    (Ω : Type) [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    {k : Type} [Field k] [Algebra k U.functionField]
    (v : Place k U.functionField)
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [Q.IsMaximal]
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
    ∀ (r : Place k L), r.restrict K = v →
      ∃ (σ : Gal(Ω/K)) (P : HeightOneSpectrum (Place.integralClosureAt L v)),
        P.asIdeal = absoluteNormalizationPrimeContraction
          (A := v.toValuationSubring) (L := L) (Omega := Ω) (σ • Q) ∧
        Place.placeOfPrime P = r ∧
        let R := (Place.placeOfPrime P).toValuationSubring
        let QB := (σ • Q).comap (normalizationIntegralBaseRingEquiv
          v.toValuationSubring (Place.integralClosureAt L v) Ω).toRingHom
        let q := QB.map
          (normalizationBaseLocalizationRingMap (Place.integralClosureAt L v) R Ω)
        q.IsMaximal ∧
          (genericPlaceInertia W.left (Place.placeOfPrime P) q).map i =
            (genericPlaceInertia U v Q).map
              (MulAut.conj (absoluteGenericGaloisToFundamentalGroup U Ω σ)).toMonoidHom ⊓
                i.range := by
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
  change ∀ (r : Place k L), r.restrict K = v → _
  intro r hr
  let P := Place.fiberCenter L v hr
  obtain ⟨σ, hσ⟩ := exists_smul_absoluteNormalizationPrimeContraction_eq v P Q
  have hP : P.asIdeal = absoluteNormalizationPrimeContraction
      (A := v.toValuationSubring) (L := L) (Omega := Ω) (σ • Q) := hσ.symm
  have hPr : Place.placeOfPrime P = r := by
    exact Place.eq_of_fiberCenter_eq (Place.restrict_placeOfPrime P) hr
      (Place.fiberCenter_placeOfPrime P)
  let Qσ : Ideal (integralClosure v.toValuationSubring Ω) := σ • Q
  let : Qσ.IsMaximal := by
    change (σ • Q).IsMaximal
    rw [Ideal.pointwise_smul_eq_comap]
    exact Ideal.comap_isMaximal_of_surjective _
      (MulSemiringAction.toRingAut Gal(Ω/K)
        (integralClosure v.toValuationSubring Ω) σ).symm.surjective
  refine ⟨σ, P, hP, hPr, ?_⟩
  have hactual := connectedCover_actualPlaceInertia_image Ω v Qσ W w P hP
  have hconj : genericPlaceInertia U v Qσ =
      (genericPlaceInertia U v Q).map
        (MulAut.conj (absoluteGenericGaloisToFundamentalGroup U Ω σ)).toMonoidHom := by
    rw [genericPlaceInertia_eq_absoluteInertiaImage U v Qσ,
      genericPlaceInertia_eq_absoluteInertiaImage U v Q]
    exact inertia_smul_map Q σ (absoluteGenericGaloisToFundamentalGroup U Ω)
  exact ⟨hactual.1, hactual.2.trans (congrArg (fun A => A ⊓ i.range) hconj)⟩

end EtaleFundamentalGroups.Inertia
