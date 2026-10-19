/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.SameModelPointedInertia
import Nyll.AnabelianGeometry.WeightFiltration.SchemeIsoBoundaryInertia
import Nyll.AnabelianGeometry.WeightFiltration.NamedModelCoverGroupSquare
import Nyll.AlgebraicCurves.Models.Ramification.OpenBoundary
import Mathlib.Logic.Equiv.Set

/-! # Actual model isomorphisms with one coordinate field and one ambient field

The source coordinate algebra is induced by its actual open chart. The ambient
algebra is transported backwards along the specified isomorphism. Their scalar
tower is proved from the chart square, so the same normalization prime has the
same inertia image and the same abelian range on both sides.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open AlgebraicCurve SchemeTheory EtaleFundamentalGroups.Inertia ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration
attribute [local instance] CurveModel.isIntegral normalizationCommAlgGaloisAction
  placeBaseAmbientAlgebra placeBaseAmbientTower

/-- Changing the source by an actual isomorphism does not change the omitted
places in a fixed proper model. The equality retains the place itself. -/
theorem openBoundaryPlaces_comp_iso
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) {X Y : Scheme} (i : X ≅ Y) (j : Y ⟶ M.C) :
    M.openBoundaryPlaces (i.hom ≫ j) = M.openBoundaryPlaces j := by
  ext p
  change (M.placeEquiv.symm p).val ∉ Set.range (i.hom ≫ j) ↔
    (M.placeEquiv.symm p).val ∉ Set.range j
  apply not_congr
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨i.hom x, hx⟩
  · rintro ⟨y, hy⟩
    refine ⟨i.inv y, ?_⟩
    change j (i.hom (i.inv y)) = _
    have h := congrArg (fun a : Y ⟶ Y => a y) i.inv_hom_id
    exact (congrArg j h).trans hy

/-- The actual chart algebra on the source and the transported ambient algebra
have the original coordinate-field embedding as their composite. -/
theorem sameModelIso_chart_scalarTower
    {K F Ω : Type} [Field K] [Field F] [Algebra K F] [Field Ω]
    (M : CurveModel K F) {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (i : X ≅ Y) (j : Y ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    [Algebra F Y.functionField]
    (hfield : algebraMap F Y.functionField = (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    [Algebra Y.functionField Ω] [Algebra F Ω] [IsScalarTower F Y.functionField Ω] :
    let jX := i.hom ≫ j
    let hjX : DenseRange jX :=
      jX.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace jX
    let _AFX : Algebra F X.functionField :=
      ((jX.functionFieldMap hjX).comp M.ffEquiv.toRingHom).toAlgebra
    let _AXΩ : Algebra X.functionField Ω := namedBaseTransportAmbientAlgebra i.symm Ω
    IsScalarTower F X.functionField Ω := by
  intro jX hjX AFX AXΩ
  have hchart : i.inv ≫ jX = j := i.inv_hom_id_assoc j
  have hmap := namedBaseTransport_chart_functionFieldMap i.symm j jX hj hjX hchart
  apply IsScalarTower.of_algebraMap_eq
  intro z
  calc
    algebraMap F Ω z = algebraMap Y.functionField Ω (algebraMap F Y.functionField z) :=
      IsScalarTower.algebraMap_apply F Y.functionField Ω z
    _ = algebraMap Y.functionField Ω (j.functionFieldMap hj (M.ffEquiv z)) :=
      congrArg (algebraMap Y.functionField Ω) (DFunLike.congr_fun hfield z)
    _ = algebraMap X.functionField Ω (algebraMap F X.functionField z) := by
      change algebraMap Y.functionField Ω (j.functionFieldMap hj (M.ffEquiv z)) =
        algebraMap Y.functionField Ω
          (i.inv.functionFieldMap i.inv.homeomorph.surjective.denseRange
            (jX.functionFieldMap hjX (M.ffEquiv z)))
      exact congrArg (algebraMap Y.functionField Ω) (DFunLike.congr_fun hmap (M.ffEquiv z)).symm

/-- Backward transport of the same ambient field along an actual model
isomorphism carries every prescribed original place inertia exactly. In
particular its abelian range retains the same place, without a new label
choice or an inertia-preservation hypothesis. -/
theorem sameModelIso_prescribedPrime_inertia
    {K F Ω : Type} [Field K] [Field F] [Algebra K F] [Field Ω]
    (M : CurveModel K F) {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (i : X ≅ Y) (j : Y ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    [Algebra F Y.functionField]
    (hfield : algebraMap F Y.functionField = (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    [Algebra Y.functionField Ω] [Algebra F Ω] [IsScalarTower F Y.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure Y.functionField Ω] [IsSepClosure F Ω] :
    let jX := i.hom ≫ j
    let hjX : DenseRange jX :=
      jX.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace jX
    let _AFX : Algebra F X.functionField :=
      ((jX.functionFieldMap hjX).comp M.ffEquiv.toRingHom).toAlgebra
    let _AXΩ : Algebra X.functionField Ω := namedBaseTransportAmbientAlgebra i.symm Ω
    let _hFXΩ : IsScalarTower F X.functionField Ω :=
      sameModelIso_chart_scalarTower M i j hj hfield
    let _hSepX : IsSepClosure X.functionField Ω := namedBaseTransport_isSepClosure i.symm Ω
    let hpoint := sameModel_genericPoint_comp M jX j hjX hj rfl hfield i.hom rfl
    let ψ := pointedFundamentalGroupHom i.hom (X.genericExtensionMorphism Ω)
      (Y.genericExtensionMorphism Ω) hpoint
    ∀ (p : Place K F) [Algebra p.toValuationSubring Ω]
      [IsScalarTower p.toValuationSubring F Ω]
      (Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω)),
      (genericPlaceInertia X p Q).map ψ.toMonoidHom = genericPlaceInertia Y p Q ∧
      ((genericPlaceInertia X p Q).map
        (TopologicalAbelianization.mk π₁ᵉᵗ(X.genericExtensionMorphism Ω))).map
          (TopologicalAbelianization.map ψ).toMonoidHom =
        (genericPlaceInertia Y p Q).map
          (TopologicalAbelianization.mk π₁ᵉᵗ(Y.genericExtensionMorphism Ω)) := by
  intro jX hjX AFX AXΩ hFXΩ hSepX hpoint ψ p ApΩ hpΩ Q
  exact sameModel_pointed_inertia_image M jX j hjX hj rfl hfield i.hom rfl p Q


/-- The actual pointed equivalence transports the boundary coordinate range
of the unchanged place. The source prime family is the target prime family
on the literally equal boundary set. Thus the same cusp bijection can be
returned through two model isomorphisms without relabeling its places. -/
theorem sameModelIso_boundary_range
    {K F Ω : Type} [Field K] [CharZero K] [IsAlgClosed K]
    [Field F] [Algebra K F] [Field Ω]
    (M : CurveModel K F) {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (i : X ≅ Y) (j : Y ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    [Algebra F Y.functionField]
    (hfield : algebraMap F Y.functionField = (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    [Algebra Y.functionField Ω] [Algebra F Ω] [IsScalarTower F Y.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure Y.functionField Ω] [IsSepClosure F Ω]
    [Algebra K Ω] [IsScalarTower K F Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal] :
    let jX := i.hom ≫ j
    let hjX : DenseRange jX :=
      jX.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace jX
    let _AFX : Algebra F X.functionField :=
      ((jX.functionFieldMap hjX).comp M.ffEquiv.toRingHom).toAlgebra
    let _AXΩ : Algebra X.functionField Ω := namedBaseTransportAmbientAlgebra i.symm Ω
    let _hFXΩ : IsScalarTower F X.functionField Ω :=
      sameModelIso_chart_scalarTower M i j hj hfield
    let _hSepX : IsSepClosure X.functionField Ω := namedBaseTransport_isSepClosure i.symm Ω
    let E := Set.equivOfEq (openBoundaryPlaces_comp_iso M i j)
    let QX : ∀ p : M.openBoundaryPlaces jX,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω) := fun p => Q (E p)
    let _hQX : ∀ p, (QX p).IsMaximal := fun p => inferInstanceAs ((Q (E p)).IsMaximal)
    let hpoint := sameModel_genericPoint_comp M jX j hjX hj rfl hfield i.hom rfl
    let B := namedModelPointedGroupEquiv i (X.genericExtensionMorphism Ω)
      (Y.genericExtensionMorphism Ω) hpoint
    ∀ p : M.openBoundaryPlaces jX,
      ((boundaryPlaceInertiaHom M jX hjX rfl QX p).toMonoidHom.range).map
          (TopologicalAbelianization.congr B).toMonoidHom =
        (boundaryPlaceInertiaHom M j hj hfield Q (E p)).toMonoidHom.range := by
  intro jX hjX AFX AXΩ hFXΩ hSepX E QX hQX hpoint B p
  let ψ := pointedFundamentalGroupHom i.hom (X.genericExtensionMorphism Ω)
    (Y.genericExtensionMorphism Ω) hpoint
  have hAb : (TopologicalAbelianization.congr B).toMonoidHom =
      (TopologicalAbelianization.map ψ).toMonoidHom := by
    apply MonoidHom.ext
    intro z
    obtain ⟨v, rfl⟩ := TopologicalAbelianization.surjective_mk _ z
    change TopologicalAbelianization.congr B (TopologicalAbelianization.mk _ v) =
      TopologicalAbelianization.map ψ (TopologicalAbelianization.mk _ v)
    rw [TopologicalAbelianization.congr_apply_mk, TopologicalAbelianization.map_apply_mk]
    exact congrArg (TopologicalAbelianization.mk _) (namedModelPointedGroupEquiv_apply
      i (X.genericExtensionMorphism Ω) (Y.genericExtensionMorphism Ω) hpoint v)
  rw [boundaryPlaceInertiaHom_range M jX hjX rfl QX p,
    boundaryPlaceInertiaHom_range M j hj hfield Q (E p), hAb]
  exact (sameModel_pointed_inertia_image M jX j hjX hj rfl hfield i.hom rfl
    p.val (QX p)).2

end AnabelianGeometry.WeightFiltration
