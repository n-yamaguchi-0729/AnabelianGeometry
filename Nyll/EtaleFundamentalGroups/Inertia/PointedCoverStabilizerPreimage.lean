/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.GenericGaloisMapComparison
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisPoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.ExtendedFiberGaloisAction

/-! # Absolute generic preimages of arbitrary connected-cover stabilizers -/

noncomputable section
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

private theorem genericPointLiftPrecomp_left_connectedCover
    {U : Scheme.{u}} [IsIntegral U]
    {Ω : Type u} [Field Ω] [Algebra U.functionField Ω] [IsSepClosed Ω]
    (W : FiniteEtale U) (g : Over.mk (U.genericExtensionMorphism Ω) ⟶ W.toComma)
    (σ : Gal(Ω/U.functionField)) :
    Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫ g.left =
      (genericPointLiftPrecomp W g σ).left := by
  let baseIso : (Over.mk (U.genericExtensionMorphism Ω)).left ≅ Spec (.of Ω) :=
    eqToIso (Over.mk_left (U.genericExtensionMorphism Ω))
  apply (cancel_epi baseIso.inv).1
  change Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫
      (baseIso.inv ≫ g.left) = baseIso.inv ≫ (genericPointLiftPrecomp W g σ).left
  symm
  change (eqToIso (Over.mk_left (U.genericExtensionMorphism Ω))).inv ≫
    (genericPointLiftPrecomp W g σ).left = _
  rfl

private theorem absoluteGenericGalois_fiberLift
    {U : Scheme.{u}} [IsIntegral U]
    (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    (W : FiniteEtale U) (w : (fiber (U.genericExtensionMorphism Ω)).obj W)
    (σ : Gal(Ω/U.functionField)) :
    fiberObjEquivHom (U.genericExtensionMorphism Ω) W
      ((absoluteGenericGaloisToFundamentalGroup U Ω σ).hom.app W w) =
      genericPointLiftPrecomp W
        (fiberObjEquivHom (U.genericExtensionMorphism Ω) W w) σ := by
  apply Over.OverMorphism.ext
  rw [← genericPointLiftPrecomp_left_connectedCover]
  rw [absoluteGenericGaloisToFundamentalGroup_eq_fieldSourceAbsoluteGaloisHom]
  exact fundamentalGroupHom_point_of_point_action
    (U.fromSpecStalk (genericPoint U)) (ξ U.functionField Ω)
    (suppliedGaloisEquivFundamentalGroup U.functionField Ω σ) σ.toRingHom
    (suppliedGaloisEquivFundamentalGroup_point U.functionField Ω σ) W w

/-- The specified point stabilizer pulls back to its actual function-field subgroup,
without a Galois-cover assumption. -/
theorem pointedCoverStabilizer_comap_absoluteGenericGalois
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
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
    (MulAction.stabilizer π₁ᵉᵗ(U.genericExtensionMorphism Ω) w).comap
      (absoluteGenericGaloisToFundamentalGroup U Ω) =
      (AlgEquiv.restrictScalarsHom K : Gal(Ω/L) →* Gal(Ω/K)).range := by
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
  let e : (fiber (U.genericExtensionMorphism Ω)).obj W ≃ (L →ₐ[K] Ω) :=
    (fiberObjEquivHom (U.genericExtensionMorphism Ω) W).trans
      (finiteEtaleGenericHomEquivFunctionFieldAlgHom (Ω := Ω) W)
  change (MulAction.stabilizer π₁ᵉᵗ(U.genericExtensionMorphism Ω) w).comap
      (absoluteGenericGaloisToFundamentalGroup U Ω) =
    (AlgEquiv.restrictScalarsHom K : Gal(Ω/L) →* Gal(Ω/K)).range
  ext σ
  change (absoluteGenericGaloisToFundamentalGroup U Ω σ).hom.app W w = w ↔
    σ ∈ (AlgEquiv.restrictScalarsHom K : Gal(Ω/L) →* Gal(Ω/K)).range
  have he : e ((absoluteGenericGaloisToFundamentalGroup U Ω σ).hom.app W w) =
      σ.toAlgHom.comp j := by
    change finiteEtaleGenericHomFunctionFieldAlgHom W
      (fiberObjEquivHom (U.genericExtensionMorphism Ω) W
        ((absoluteGenericGaloisToFundamentalGroup U Ω σ).hom.app W w)) = σ.toAlgHom.comp j
    rw [absoluteGenericGalois_fiberLift]
    exact finiteEtaleGenericHomFunctionFieldAlgHom_precomp W g σ
  constructor
  · intro hσ
    have hj : σ.toAlgHom.comp j = j := by
      calc
        σ.toAlgHom.comp j =
            e ((absoluteGenericGaloisToFundamentalGroup U Ω σ).hom.app W w) := he.symm
        _ = e w := congrArg e hσ
        _ = j := rfl
    let τ : Gal(Ω/L) := { σ with commutes' := fun z => DFunLike.congr_fun hj z }
    exact ⟨τ, AlgEquiv.ext (fun _ => rfl)⟩
  · rintro ⟨τ, rfl⟩
    apply e.injective
    rw [he]
    change (τ.restrictScalars K).toAlgHom.comp j = j
    apply AlgHom.ext
    intro z
    exact τ.commutes z

end EtaleFundamentalGroups.Inertia
