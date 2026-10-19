/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.PointedCoverFieldPreimage
import Nyll.EtaleFundamentalGroups.Inertia.InertiaImageIntersection
import Nyll.EtaleFundamentalGroups.Inertia.GenericGaloisNaturality
import Nyll.EtaleFundamentalGroups.Inertia.SamePointedCoverImage

/-!
# Images of restricted inertia in the actual pointed cover

The prescribed lift determines the cover map and field restriction. The
image of every restricted subgroup is its exact intersection with the
actual cover image.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

private theorem genericExtension_point_comp
    (U : Scheme.{u}) [IsIntegral U]
    (Ω : Type u) [Field Ω] [Algebra U.functionField Ω] :
    ξ U.functionField Ω ≫ U.genericExtensionMorphism U.functionField =
      U.genericExtensionMorphism Ω := by
  simp only [Scheme.genericExtensionMorphism]
  rw [← Spec.map_comp_assoc]
  congr 1

variable {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
  [IsLocallyNoetherian U] [ConnectedSpace U]
  (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
  [IsSepClosure U.functionField Ω] [IsSepClosed Ω]

/-- For the actual pointed cover map, the image of a restricted subgroup
is its original image intersected with the same actual cover image. -/
theorem pointedCover_restrictedSubgroup_image
    (W : FiniteEtale U) (hW : IsGalois W)
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W)
    (I : Subgroup Gal(Ω/U.functionField)) :
    letI : IsGalois W := hW
    letI : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let K := U.functionField
    let L := W.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra W
    letI : FiniteDimensional K L :=
      finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : _root_.IsGalois K L := isGalois_functionField_of_isGalois_finiteEtale W hW
    let h := genericExtension_point_comp U Ω
    let x := (absoluteGenericFiberIso U Ω).inv.app W w
    let g := genericPointLiftRebase h W
      (fiberObjEquivHom (ξ K Ω ≫ U.genericExtensionMorphism K) W x)
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
    let qL := (fieldSourceAbsoluteGaloisHom L Ω jL).toMonoidHom
    let r : Gal(Ω/L) →* Gal(Ω/K) := AlgEquiv.restrictScalarsHom K
    ((I.comap r).map qL).map i =
      I.map (absoluteGenericGaloisToFundamentalGroup U Ω) ⊓ i.range := by
  let : IsGalois W := hW
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let K := U.functionField
  let L := W.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra W
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : _root_.IsGalois K L := isGalois_functionField_of_isGalois_finiteEtale W hW
  let h := genericExtension_point_comp U Ω
  let x := (absoluteGenericFiberIso U Ω).inv.app W w
  let g := genericPointLiftRebase h W
    (fiberObjEquivHom (ξ K Ω ≫ U.genericExtensionMorphism K) W x)
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
  let qL := (fieldSourceAbsoluteGaloisHom L Ω jL).toMonoidHom
  let r : Gal(Ω/L) →* Gal(Ω/K) := AlgEquiv.restrictScalarsHom K
  change ((I.comap r).map qL).map i =
    I.map (absoluteGenericGaloisToFundamentalGroup U Ω) ⊓ i.range
  have hi : i.range = (finiteEtaleGaloisCoverQuotientMonoidHom
      (U.genericExtensionMorphism Ω) W hW w).ker :=
    pointedCover_sameGenericLift_range Ω W hW w
  have hsquare : i.comp qL =
      (absoluteGenericGaloisToFundamentalGroup U Ω).comp r := by
    apply MonoidHom.ext
    intro σ
    exact pointedFundamentalGroupHom_fieldSource_eq_absoluteGenericGalois
      (U := U) (V := W.left) L Ω W.hom jL hpoint σ
  rw [hi, Subgroup.map_map, hsquare]
  exact inertia_image_eq_intersection r
    (absoluteGenericGaloisToFundamentalGroup U Ω)
    (finiteEtaleGaloisCoverQuotientMonoidHom
      (U.genericExtensionMorphism Ω) W hW w).ker
    (pointedCoverKernel_comap_absoluteGenericGalois Ω W hW w).symm I

end EtaleFundamentalGroups.Inertia
