/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.PointedCoverFieldPreimage
import Nyll.EtaleFundamentalGroups.Inertia.GenericLiftPointComparison
import Nyll.EtaleFundamentalGroups.GeometricFiber.PointedCoverImage
import Nyll.EtaleFundamentalGroups.Inertia.GenericGaloisNaturality

/-!
# The actual cover image at the prescribed generic lift

The reconstructed source point is the originally selected fibre point,
so the actual covering map has the kernel of the same deck quotient as image.
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

/-- The original point determines both the canonical covering map and the
pointed deck quotient, whose kernel is exactly the covering map image. -/
theorem pointedCover_sameGenericLift_range
    (W : FiniteEtale U) (hW : IsGalois W)
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
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
    i.range = (finiteEtaleGaloisCoverQuotientMonoidHom
      (U.genericExtensionMorphism Ω) W hW w).ker := by
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
  change i.range = (finiteEtaleGaloisCoverQuotientMonoidHom
    (U.genericExtensionMorphism Ω) W hW w).ker
  have hg : g = fiberObjEquivHom (U.genericExtensionMorphism Ω) W w :=
    genericPointLiftRebase_absoluteGenericFiberIso Ω h W w
  have hrec : ξ L Ω ≫ jL =
      (eqToIso (Over.mk_left (U.genericExtensionMorphism Ω))).inv ≫ g.left :=
    finiteEtaleGenericHomFunctionFieldAlgHom_spec W g
  have hw : (fiberObjEquivHom (U.genericExtensionMorphism Ω) W).symm
      (Over.homMk (ξ L Ω ≫ jL) hpoint) = w := by
    apply (fiberObjEquivHom (U.genericExtensionMorphism Ω) W).injective
    rw [Equiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    change ξ L Ω ≫ jL =
      (fiberObjEquivHom (U.genericExtensionMorphism Ω) W w).left
    rw [hg] at hrec
    exact hrec
  change (pointedFundamentalGroupHom W.hom (ξ L Ω ≫ jL)
    (U.genericExtensionMorphism Ω) hpoint).toMonoidHom.range = _
  rw [pointedFundamentalGroupHom_range_eq_stabilizer, hw]
  exact (finiteEtaleGaloisCoverQuotientMonoidHom_ker
    (U.genericExtensionMorphism Ω) W hW w).symm

end EtaleFundamentalGroups.Inertia
