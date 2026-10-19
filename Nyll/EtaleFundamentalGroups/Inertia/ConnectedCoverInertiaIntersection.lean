/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.PointedCoverStabilizerPreimage
import Nyll.EtaleFundamentalGroups.Inertia.InertiaImageIntersection
import Nyll.EtaleFundamentalGroups.Inertia.GenericGaloisNaturality
import Nyll.EtaleFundamentalGroups.Inertia.SameConnectedCoverImage

/-!
# Restricted inertia images for arbitrary connected pointed covers

The prescribed lift determines the cover map and field restriction. The
image of every restricted subgroup is its exact intersection with the
actual cover image.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

variable {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
  [IsLocallyNoetherian U] [ConnectedSpace U]
  (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
  [IsSepClosure U.functionField Ω] [IsSepClosed Ω]

/-- For the actual pointed cover map, the image of a restricted subgroup
is its original image intersected with the same actual cover image. -/
theorem connectedCover_restrictedSubgroup_image
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W)
    (I : Subgroup Gal(Ω/U.functionField)) :
    letI : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let K := U.functionField
    let L := W.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra W
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
    let qL := (fieldSourceAbsoluteGaloisHom L Ω jL).toMonoidHom
    let r : Gal(Ω/L) →* Gal(Ω/K) := AlgEquiv.restrictScalarsHom K
    ((I.comap r).map qL).map i =
      I.map (absoluteGenericGaloisToFundamentalGroup U Ω) ⊓ i.range := by
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let K := U.functionField
  let L := W.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra W
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
  let qL := (fieldSourceAbsoluteGaloisHom L Ω jL).toMonoidHom
  let r : Gal(Ω/L) →* Gal(Ω/K) := AlgEquiv.restrictScalarsHom K
  change ((I.comap r).map qL).map i =
    I.map (absoluteGenericGaloisToFundamentalGroup U Ω) ⊓ i.range
  have hi : i.range = MulAction.stabilizer π₁ᵉᵗ(U.genericExtensionMorphism Ω) w :=
    connectedCover_sameGenericLift_range Ω W w
  have hsquare : i.comp qL =
      (absoluteGenericGaloisToFundamentalGroup U Ω).comp r := by
    apply MonoidHom.ext
    intro σ
    exact pointedFundamentalGroupHom_fieldSource_eq_absoluteGenericGalois
      (U := U) (V := W.left) L Ω W.hom jL hpoint σ
  rw [hi, Subgroup.map_map, hsquare]
  exact inertia_image_eq_intersection r
    (absoluteGenericGaloisToFundamentalGroup U Ω)
    (MulAction.stabilizer π₁ᵉᵗ(U.genericExtensionMorphism Ω) w)
    (pointedCoverStabilizer_comap_absoluteGenericGalois Ω W w).symm I

end EtaleFundamentalGroups.Inertia
