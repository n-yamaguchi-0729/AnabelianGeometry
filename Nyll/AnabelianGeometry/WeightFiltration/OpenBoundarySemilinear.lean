/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Models.Ramification.OpenBoundary
import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearFunctionField
import Nyll.AnabelianGeometry.WeightFiltration.GenericPointNaturality

/-!
# Semilinear compatibility of an actual open curve

A commuting square of curve isomorphisms preserves the omitted places and
intertwines the actual function-field maps. The point action is the original
one supplied by the semilinear curve-model comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory NeronModelInfra

namespace AlgebraicCurve.CurveModel

/-- Restriction of an actual semilinear curve isomorphism preserves the
boundary and the induced function-field action. -/
theorem openBoundary_semilinear_compatibility
    {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F)
    {X : Scheme} [IsIntegral X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (θX : X ≅ X) (θ : M.C ≅ M.C)
    (σ : K ≃+* K) (g : SemilinearAut K F)
    (hbase : θ.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
    (hsquare : θX.hom ≫ j = j ≫ θ.hom)
    (hpoint : ∀ x y : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase,
      y.val ≫ θ.hom = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.val →
        M.pointEquivPlace y = g • M.pointEquivPlace x)
    (hfield : ∀ z : F, θ.hom.functionFieldRingEquivOfIsOpenImmersion (M.ffEquiv z) =
      M.ffEquiv (SemilinearAut.toRingAut g z)) :
    (∀ p : Place K F, p ∈ M.openBoundaryPlaces j ↔ g • p ∈ M.openBoundaryPlaces j) ∧
      ∀ z : F, θX.hom.functionFieldRingEquivOfIsOpenImmersion
          (j.functionFieldMap hj (M.ffEquiv z)) =
        j.functionFieldMap hj (M.ffEquiv (SemilinearAut.toRingAut g z)) := by
  classical
  have hcomm (x : X) : j (θX.hom x) = θ.hom (j x) :=
    congrArg (fun f : X ⟶ M.C => f x) hsquare
  have hinv (z : M.C) : θ.hom (θ.inv z) = z :=
    congrArg (fun f : M.C ⟶ M.C => f z) θ.inv_hom_id
  have hXin (x : X) : θX.hom (θX.inv x) = x :=
    congrArg (fun f : X ⟶ X => f x) θX.inv_hom_id
  have hrange (z : M.C) : θ.inv z ∈ Set.range j ↔ z ∈ Set.range j := by
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨θX.hom x, (hcomm x).trans ((congrArg θ.hom hx).trans (hinv z))⟩
    · rintro ⟨x, hx⟩
      refine ⟨θX.inv x, θ.hom.isOpenEmbedding.injective ?_⟩
      exact (hcomm (θX.inv x)).symm.trans
        ((congrArg j (hXin x)).trans (hx.trans (hinv z).symm))
  have hclosed (x : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase) :
      (M.placeEquiv.symm (M.pointEquivPlace x)).val = x.val (IsLocalRing.closedPoint K) := by
    change (M.placeEquiv.symm (M.placeEquiv (pointEquivClosedPoint M.toBase x))).val = _
    rw [M.placeEquiv.symm_apply_apply]
    rfl
  let e := Scheme.Spec.mapIso σ.toCommRingCatIso.op
  have hbase' : θ.inv ≫ M.toBase = M.toBase ≫ e.inv := by
    apply (cancel_mono e.hom).1
    calc
      (θ.inv ≫ M.toBase) ≫ e.hom = θ.inv ≫ (M.toBase ≫ e.hom) := Category.assoc _ _ _
      _ = θ.inv ≫ (θ.hom ≫ M.toBase) := congrArg (θ.inv ≫ ·) hbase.symm
      _ = M.toBase := θ.inv_hom_id_assoc _
      _ = (M.toBase ≫ e.inv) ≫ e.hom :=
        ((Category.assoc M.toBase e.inv e.hom).trans
          ((congrArg (M.toBase ≫ ·) e.inv_hom_id).trans
            (CategoryTheory.Category.comp_id M.toBase))).symm
  have hplace (p : Place K F) :
      (M.placeEquiv.symm (g • p)).val = θ.inv ((M.placeEquiv.symm p).val) := by
    let x := M.pointEquivPlace.symm p
    let y : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase :=
      ⟨e.hom ≫ x.val ≫ θ.inv, by
        calc
          (e.hom ≫ x.val ≫ θ.inv) ≫ M.toBase = e.hom ≫ x.val ≫ M.toBase ≫ e.inv := by
            simp only [Category.assoc, hbase']
          _ = e.hom ≫ e.inv := by
            rw [← Category.assoc x.val M.toBase e.inv, x.property, Category.id_comp]
          _ = 𝟙 _ := e.hom_inv_id⟩
    have hy : y.val ≫ θ.hom = e.hom ≫ x.val := by
      change (e.hom ≫ x.val ≫ θ.inv) ≫ θ.hom = _
      simp only [Category.assoc, θ.inv_hom_id, Category.comp_id]
    have hgp := hpoint x y hy
    have hx : M.pointEquivPlace x = p := M.pointEquivPlace.apply_symm_apply p
    rw [hx] at hgp
    rw [← hgp, hclosed]
    change θ.inv (x.val (e.hom (IsLocalRing.closedPoint K))) = _
    have he : e.hom (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint K :=
      AlgebraicGeometry.Spec_closedPoint
    rw [he]
    have hxp := hclosed x
    rw [hx] at hxp
    exact congrArg θ.inv hxp.symm
  refine ⟨?_, ?_⟩
  · intro p
    change (M.placeEquiv.symm p).val ∉ Set.range j ↔
      (M.placeEquiv.symm (g • p)).val ∉ Set.range j
    rw [hplace, hrange]
  · let qX := X.fromSpecStalk (genericPoint X)
    let qM := M.C.fromSpecStalk (genericPoint M.C)
    let φX := θX.hom.functionFieldRingEquivOfIsOpenImmersion.toRingHom
    let φM := θ.hom.functionFieldRingEquivOfIsOpenImmersion.toRingHom
    have hdX : DenseRange θX.hom :=
      θX.hom.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _
    have hdM : DenseRange θ.hom :=
      θ.hom.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _
    have hX : Spec.map (CommRingCat.ofHom φX) ≫ qX = qX ≫ θX.hom :=
      AnabelianGeometry.WeightFiltration.functionFieldMap_genericPoint θX.hom hdX
    have hM : Spec.map (CommRingCat.ofHom φM) ≫ qM = qM ≫ θ.hom :=
      AnabelianGeometry.WeightFiltration.functionFieldMap_genericPoint θ.hom hdM
    have hjg := AnabelianGeometry.WeightFiltration.functionFieldMap_genericPoint j hj
    have hmap : φX.comp (j.functionFieldMap hj) = (j.functionFieldMap hj).comp φM := by
      have hspec : Spec.map (CommRingCat.ofHom (φX.comp (j.functionFieldMap hj))) =
          Spec.map (CommRingCat.ofHom ((j.functionFieldMap hj).comp φM)) := by
        apply (cancel_mono qM).1
        change (Spec.map (CommRingCat.ofHom (j.functionFieldMap hj) ≫ CommRingCat.ofHom φX)) ≫ qM =
          (Spec.map (CommRingCat.ofHom φM ≫ CommRingCat.ofHom (j.functionFieldMap hj))) ≫ qM
        rw [Spec.map_comp, Spec.map_comp, Category.assoc, hjg, ← Category.assoc, hX,
          Category.assoc, hsquare, ← Category.assoc qX j θ.hom, ← hjg]
        simp only [Category.assoc]
        rw [hM]
      exact congrArg
        (fun f : CommRingCat.of M.C.functionField ⟶ CommRingCat.of X.functionField => f.hom)
        (Spec.map_injective hspec)
    intro z
    have hz := DFunLike.congr_fun hmap (M.ffEquiv z)
    change θX.hom.functionFieldRingEquivOfIsOpenImmersion
      (j.functionFieldMap hj (M.ffEquiv z)) =
        j.functionFieldMap hj (θ.hom.functionFieldRingEquivOfIsOpenImmersion (M.ffEquiv z)) at hz
    exact hz.trans (congrArg (j.functionFieldMap hj) (hfield z))

end AlgebraicCurve.CurveModel
