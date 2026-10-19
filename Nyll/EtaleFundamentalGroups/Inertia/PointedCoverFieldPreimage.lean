/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteDivisorialFiniteQuotientNaturality
import Nyll.EtaleFundamentalGroups.Inertia.NormalRestrictionKernel

/-!
# The exact field preimage of the same pointed cover subgroup

The chosen geometric lift supplies both the field embedding and the deck
quotient. Its kernel pulls back to exactly the scalar-restriction image.
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

/-- The actual pointed deck kernel has exactly the prescribed finite-field
subgroup as its preimage under the absolute generic Galois map. -/
theorem pointedCoverKernel_comap_absoluteGenericGalois
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
    (finiteEtaleGaloisCoverQuotientMonoidHom
      (U.genericExtensionMorphism Ω) W hW w).ker.comap
        (absoluteGenericGaloisToFundamentalGroup U Ω) =
      (AlgEquiv.restrictScalarsHom K : Gal(Ω/L) →* Gal(Ω/K)).range := by
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
  change (finiteEtaleGaloisCoverQuotientMonoidHom
    (U.genericExtensionMorphism Ω) W hW w).ker.comap
      (absoluteGenericGaloisToFundamentalGroup U Ω) =
    (AlgEquiv.restrictScalarsHom K : Gal(Ω/L) →* Gal(Ω/K)).range
  rw [← normalRestriction_ker_eq_restrictScalars_range]
  ext σ
  change finiteEtaleGaloisCoverQuotientMonoidHom
      (U.genericExtensionMorphism Ω) W hW w
      (absoluteGenericGaloisToFundamentalGroup U Ω σ) = 1 ↔
    AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L σ = 1
  let e := finiteEtaleAutOpFunctionFieldMulEquiv W hW
  have hcomp : AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L σ =
      e (finiteEtaleGaloisCoverQuotientMonoidHom
        (U.genericExtensionMorphism Ω) W hW w
        (absoluteGenericGaloisToFundamentalGroup U Ω σ)) :=
    restrictNormalHom_eq_finiteEtaleAutFunctionFieldAlgEquiv_absoluteGenericGalois_rebased
      Ω W hW w σ
  constructor
  · intro hσ
    rw [hcomp, hσ]
    exact e.map_one
  · intro hσ
    apply e.injective
    rw [e.map_one]
    exact hcomp.symm.trans hσ

end EtaleFundamentalGroups.Inertia
