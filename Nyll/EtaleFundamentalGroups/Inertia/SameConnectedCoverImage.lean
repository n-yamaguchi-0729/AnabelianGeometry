/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.PointedCoverStabilizerPreimage
import Nyll.EtaleFundamentalGroups.GeometricFiber.PointedCoverImage
import Nyll.EtaleFundamentalGroups.Inertia.GenericGaloisNaturality

/-! # The actual image at a prescribed point of any connected finite cover -/

noncomputable section
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The actual covering map has exactly the stabilizer of the same selected point. -/
theorem connectedCover_sameGenericLift_range
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U]
    (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
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
    let jL := W.left.fromSpecStalk (genericPoint W.left)
    let hpoint : (ξ L Ω ≫ jL) ≫ W.hom = U.genericExtensionMorphism Ω :=
      finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W g
    let i := (pointedFundamentalGroupHom W.hom (ξ L Ω ≫ jL)
      (U.genericExtensionMorphism Ω) hpoint).toMonoidHom
    i.range = MulAction.stabilizer π₁ᵉᵗ(U.genericExtensionMorphism Ω) w := by
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
  let jL := W.left.fromSpecStalk (genericPoint W.left)
  let hpoint : (ξ L Ω ≫ jL) ≫ W.hom = U.genericExtensionMorphism Ω :=
    finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W g
  have hrec : ξ L Ω ≫ jL =
      (eqToIso (Over.mk_left (U.genericExtensionMorphism Ω))).inv ≫ g.left :=
    finiteEtaleGenericHomFunctionFieldAlgHom_spec W g
  have hw : (fiberObjEquivHom (U.genericExtensionMorphism Ω) W).symm
      (Over.homMk (ξ L Ω ≫ jL) hpoint) = w := by
    apply (fiberObjEquivHom (U.genericExtensionMorphism Ω) W).injective
    rw [Equiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    change ξ L Ω ≫ jL = (fiberObjEquivHom (U.genericExtensionMorphism Ω) W w).left
    exact hrec
  change (pointedFundamentalGroupHom W.hom (ξ L Ω ≫ jL)
    (U.genericExtensionMorphism Ω) hpoint).toMonoidHom.range = _
  rw [pointedFundamentalGroupHom_range_eq_stabilizer, hw]

end EtaleFundamentalGroups.Inertia
