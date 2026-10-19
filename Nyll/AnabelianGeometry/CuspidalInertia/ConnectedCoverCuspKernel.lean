/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.CuspidalInertia.ConnectedCoverCuspRanges
import Nyll.AnabelianGeometry.CuspidalInertia.RelativeAbelianizationRelations
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaGeneration
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral

/-! # Relative cuspidal relations are actual compactification kernels -/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve IsDedekindDomain SchemeTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open AnabelianGeometry.WeightFiltration AnabelianGeometry.CuspidalInertia
open ProCGroups.Abelian

namespace EtaleFundamentalGroups.Inertia

attribute [local instance]
  placeBaseAmbientAlgebra placeBaseAmbientTower
  extendingPlaceAmbientAlgebra extendingPlaceAmbientTower
  connectedCoverPlaceConstantAmbientTower
  CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The relative relation for the base cusp saturation is the preimage of
this actual connected cover's compactification kernel. The model, point,
field embedding and covering inclusion are those of the actual cover.
No preservation or boundary-comparison equality is an input. -/
theorem connectedCover_relativeRelation_eq_compactificationKernel_with_base
    {κ : Type} [Field κ] [CharZero κ] [IsAlgClosed κ]
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U] [CompactSpace U]
    [Algebra κ U.functionField] [IsCurveOver κ U.functionField]
    {Ω : Type} [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    [Algebra κ Ω] [IsScalarTower κ U.functionField Ω]
    (M : CurveModel κ U.functionField)
    (jU : U ⟶ M.C) [IsOpenImmersion jU]
    [QuasiCompact jU] [QuasiSeparated jU]
    (hjU : DenseRange jU)
    (hbase : algebraMap U.functionField U.functionField =
      (jU.functionFieldMap hjU).comp M.ffEquiv.toRingHom)
    (Qfamily : ∀ p : M.openBoundaryPlaces jU,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [hQfamily : ∀ p, (Qfamily p).IsMaximal]
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
      ext a
      exact (j.commutes a).symm
    letI : IsSepClosure L Ω :=
      ⟨IsSepClosure.sep_closed K,
        Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
    let jL := W.left.fromSpecStalk (genericPoint W.left)
    let hpoint : (ξ L Ω ≫ jL) ≫ W.hom = U.genericExtensionMorphism Ω :=
      finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W g
    let H := π₁ᵉᵗ(ξ L Ω ≫ jL)
    let i := (pointedFundamentalGroupHom W.hom (ξ L Ω ≫ jL)
      (U.genericExtensionMorphism Ω) hpoint).toMonoidHom
    letI : Algebra κ L := ((algebraMap K L).comp (algebraMap κ K)).toAlgebra
    letI : IsScalarTower κ K L := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower κ L Ω := by
      apply IsScalarTower.of_algebraMap_eq'
      ext a
      change algebraMap κ Ω a = j (algebraMap K L (algebraMap κ K a))
      exact (IsScalarTower.algebraMap_apply κ K Ω a).trans
        (j.commutes (algebraMap κ K a)).symm
    letI : IsFiniteEtale (show W.left ⟶ U from W.hom) := W.prop
    letI : CompactSpace W.left :=
      QuasiCompact.compactSpace_of_compactSpace (show W.left ⟶ U from W.hom)
    ∃ (Mc : CurveModel κ L) (jW : W.left ⟶ Mc.C) (hopen : IsOpenImmersion jW),
      letI : IsOpenImmersion jW := hopen
      ∃ (hjW : DenseRange jW)
        (_hcover : algebraMap L L =
          (jW.functionFieldMap hjW).comp Mc.ffEquiv.toRingHom),
        (jW ≫ Mc.toBase = W.hom ≫ jU ≫ M.toBase) ∧
        (Subgroup.closure
          {h : H | i h ∈ conjugacySaturation
            (⋃ p : M.openBoundaryPlaces jU,
              (genericPlaceInertia U p.val (Qfamily p) :
                Set (Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap U.functionField Ω)) ≫
                  U.fromSpecStalk (genericPoint U))))))} ⊔
          commutator H).topologicalClosure =
          ((compactificationAbelianizationMap jW (ξ L Ω ≫ jL)).toMonoidHom.ker).comap
            (TopologicalAbelianization.mk H) := by
  classical
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let K := U.functionField
  let L := W.left.functionField
  let G := Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap U.functionField Ω)) ≫
                  U.fromSpecStalk (genericPoint U)))
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
    ext a
    exact (j.commutes a).symm
  let : IsSepClosure L Ω :=
    ⟨IsSepClosure.sep_closed K,
      Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
  let jL := W.left.fromSpecStalk (genericPoint W.left)
  let hpoint : (ξ L Ω ≫ jL) ≫ W.hom = U.genericExtensionMorphism Ω :=
    finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W g
  let H := π₁ᵉᵗ(ξ L Ω ≫ jL)
  let i : H →* G := (pointedFundamentalGroupHom W.hom (ξ L Ω ≫ jL)
    (U.genericExtensionMorphism Ω) hpoint).toMonoidHom
  let : Algebra κ L := ((algebraMap K L).comp (algebraMap κ K)).toAlgebra
  let : IsScalarTower κ K L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower κ L Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change algebraMap κ Ω a = j (algebraMap K L (algebraMap κ K a))
    exact (IsScalarTower.algebraMap_apply κ K Ω a).trans
      (j.commutes (algebraMap κ K a)).symm
  let : IsFiniteEtale (show W.left ⟶ U from W.hom) := W.prop
  let : CompactSpace W.left :=
    QuasiCompact.compactSpace_of_compactSpace (show W.left ⟶ U from W.hom)
  obtain ⟨Mc, jW, hopen, hjW, hcover, hstruct, hRanges⟩ :=
    connectedCover_abelianized_cuspSaturation_eq_boundaryRanges_with_base
      M jU hjU hbase Qfamily W w
  let : IsOpenImmersion jW := hopen
  refine ⟨Mc, jW, hopen, hjW, hcover, hstruct, ?_⟩
  let : IsCurveOver κ L :=
    AlgebraicCurve.isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      Mc.toBase Mc.ffEquiv Mc.ffEquiv_algebraMap
  let : Algebra.EssFiniteType κ L := by
    let : Algebra κ Mc.C.functionField := (baseToFunctionField Mc.toBase).toAlgebra
    let : Algebra.EssFiniteType κ Mc.C.functionField :=
      AlgebraicCurve.essFiniteType_functionField Mc.toBase
    let e : L ≃ₐ[κ] Mc.C.functionField :=
      AlgEquiv.ofRingEquiv (f := Mc.ffEquiv) Mc.ffEquiv_algebraMap
    exact (Algebra.EssFiniteType.iff_of_algEquiv e).mpr inferInstance
  choose Qc hQc using fun r : Mc.openBoundaryPlaces jW => by
    let : Nontrivial (normalizationCommAlgCat r.val.toValuationSubring Ω) :=
      (inferInstance : Nontrivial (integralClosure r.val.toValuationSubring Ω))
    exact Ideal.exists_maximal (normalizationCommAlgCat r.val.toValuationSubring Ω)
  let (r : Mc.openBoundaryPlaces jW) : (Qc r).IsMaximal := hQc r
  let S : Set G := conjugacySaturation
    (⋃ p : M.openBoundaryPlaces jU, (genericPlaceInertia U p.val (Qfamily p) : Set G))
  let T : Set H := {h : H | i h ∈ S}
  let ab := TopologicalAbelianization.mk H
  let c := compactificationAbelianizationMap jW (ξ L Ω ≫ jL)
  change (Subgroup.closure T ⊔ commutator H).topologicalClosure =
    c.toMonoidHom.ker.comap ab
  have hRanges' : ab '' T =
      ⋃ r : Mc.openBoundaryPlaces jW,
        ((boundaryPlaceInertiaHom Mc jW hjW hcover Qc r).toMonoidHom.range :
          Set (TopologicalAbelianization H)) :=
    hRanges Qc hQc
  have hker : c.toMonoidHom.ker =
      (⨆ r : Mc.openBoundaryPlaces jW,
        (genericPlaceInertia W.left r.val (Qc r)).map ab).topologicalClosure :=
    compactificationAbelianization_ker_eq_boundaryInertia_closure
      Mc jW hjW hcover Qc
  have hspan : (Subgroup.closure (ab '' T)).topologicalClosure =
      c.toMonoidHom.ker := by
    calc
      (Subgroup.closure (ab '' T)).topologicalClosure =
          (⨆ r : Mc.openBoundaryPlaces jW,
            (boundaryPlaceInertiaHom Mc jW hjW hcover Qc r).toMonoidHom.range).topologicalClosure
          := by
        rw [hRanges', Subgroup.closure_iUnion]
        simp only [Subgroup.closure_eq]
      _ = (⨆ r : Mc.openBoundaryPlaces jW,
          (genericPlaceInertia W.left r.val (Qc r)).map ab).topologicalClosure :=
        congrArg Subgroup.topologicalClosure
          (iSup_congr fun r => boundaryPlaceInertiaHom_range Mc jW hjW hcover Qc r)
      _ = c.toMonoidHom.ker := hker.symm
  rw [relativeRelation_eq_abelianization_comap, MonoidHom.map_closure]
  exact congrArg (fun B : Subgroup (TopologicalAbelianization H) => B.comap ab) hspan

/-- The original export, retaining its existing interface. -/
theorem connectedCover_relativeRelation_eq_compactificationKernel
    {κ : Type} [Field κ] [CharZero κ] [IsAlgClosed κ]
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U] [CompactSpace U]
    [Algebra κ U.functionField] [IsCurveOver κ U.functionField]
    {Ω : Type} [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    [Algebra κ Ω] [IsScalarTower κ U.functionField Ω]
    (M : CurveModel κ U.functionField)
    (jU : U ⟶ M.C) [IsOpenImmersion jU]
    [QuasiCompact jU] [QuasiSeparated jU]
    (hjU : DenseRange jU)
    (hbase : algebraMap U.functionField U.functionField =
      (jU.functionFieldMap hjU).comp M.ffEquiv.toRingHom)
    (Qfamily : ∀ p : M.openBoundaryPlaces jU,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [hQfamily : ∀ p, (Qfamily p).IsMaximal]
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
      ext a
      exact (j.commutes a).symm
    letI : IsSepClosure L Ω :=
      ⟨IsSepClosure.sep_closed K,
        Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
    let jL := W.left.fromSpecStalk (genericPoint W.left)
    let hpoint : (ξ L Ω ≫ jL) ≫ W.hom = U.genericExtensionMorphism Ω :=
      finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W g
    let H := π₁ᵉᵗ(ξ L Ω ≫ jL)
    let i := (pointedFundamentalGroupHom W.hom (ξ L Ω ≫ jL)
      (U.genericExtensionMorphism Ω) hpoint).toMonoidHom
    letI : Algebra κ L := ((algebraMap K L).comp (algebraMap κ K)).toAlgebra
    letI : IsScalarTower κ K L := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower κ L Ω := by
      apply IsScalarTower.of_algebraMap_eq'
      ext a
      change algebraMap κ Ω a = j (algebraMap K L (algebraMap κ K a))
      exact (IsScalarTower.algebraMap_apply κ K Ω a).trans
        (j.commutes (algebraMap κ K a)).symm
    letI : IsFiniteEtale (show W.left ⟶ U from W.hom) := W.prop
    letI : CompactSpace W.left :=
      QuasiCompact.compactSpace_of_compactSpace (show W.left ⟶ U from W.hom)
    ∃ (Mc : CurveModel κ L) (jW : W.left ⟶ Mc.C) (hopen : IsOpenImmersion jW),
      letI : IsOpenImmersion jW := hopen
      ∃ (hjW : DenseRange jW)
        (_hcover : algebraMap L L =
          (jW.functionFieldMap hjW).comp Mc.ffEquiv.toRingHom),
        (Subgroup.closure
          {h : H | i h ∈ conjugacySaturation
            (⋃ p : M.openBoundaryPlaces jU,
              (genericPlaceInertia U p.val (Qfamily p) :
                Set (Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap U.functionField Ω)) ≫
                  U.fromSpecStalk (genericPoint U))))))} ⊔
          commutator H).topologicalClosure =
          ((compactificationAbelianizationMap jW (ξ L Ω ≫ jL)).toMonoidHom.ker).comap
            (TopologicalAbelianization.mk H) := by
  classical
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let K := U.functionField
  let L := W.left.functionField
  let G := Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap U.functionField Ω)) ≫
                  U.fromSpecStalk (genericPoint U)))
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
    ext a
    exact (j.commutes a).symm
  let : IsSepClosure L Ω :=
    ⟨IsSepClosure.sep_closed K,
      Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
  let jL := W.left.fromSpecStalk (genericPoint W.left)
  let hpoint : (ξ L Ω ≫ jL) ≫ W.hom = U.genericExtensionMorphism Ω :=
    finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W g
  let H := π₁ᵉᵗ(ξ L Ω ≫ jL)
  let i : H →* G := (pointedFundamentalGroupHom W.hom (ξ L Ω ≫ jL)
    (U.genericExtensionMorphism Ω) hpoint).toMonoidHom
  let : Algebra κ L := ((algebraMap K L).comp (algebraMap κ K)).toAlgebra
  let : IsScalarTower κ K L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower κ L Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change algebraMap κ Ω a = j (algebraMap K L (algebraMap κ K a))
    exact (IsScalarTower.algebraMap_apply κ K Ω a).trans
      (j.commutes (algebraMap κ K a)).symm
  let : IsFiniteEtale (show W.left ⟶ U from W.hom) := W.prop
  let : CompactSpace W.left :=
    QuasiCompact.compactSpace_of_compactSpace (show W.left ⟶ U from W.hom)
  obtain ⟨Mc, jW, hopen, hjW, hcover, _hstruct, hkernel⟩ :=
    connectedCover_relativeRelation_eq_compactificationKernel_with_base
      M jU hjU hbase Qfamily W w
  exact ⟨Mc, jW, hopen, hjW, hcover, hkernel⟩

end EtaleFundamentalGroups.Inertia
