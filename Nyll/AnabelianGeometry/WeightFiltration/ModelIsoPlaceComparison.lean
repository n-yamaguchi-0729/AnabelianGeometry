/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.BoundaryModelTransport
import Nyll.SchemeTheory.FunctionFields.OpenImmersion
import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality
import Nyll.SchemeTheory.FunctionFields.ScalarFunctoriality
import Nyll.SchemeTheory.FunctionFields.StalkFunctoriality

/-! # The actual place map of a specified model isomorphism

The field equivalence is the pullback of the supplied scheme isomorphism.
Its action on places agrees with the actual map on closed points, by the
stalk range formula. Thus the boundary labels transported geometrically are
exactly the labels used in function-field inertia transport.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AnabelianGeometry.GeometricFundamentalGroup

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] CurveModel.isIntegral

variable {K F L : Type} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra K L]

/-- Pullback on function fields in the coordinates of the actual two models. -/
def modelIsoFieldEquiv
    (M : CurveModel K F) (N : CurveModel K L) (e : M.C ≅ N.C)
    (he : e.hom ≫ N.toBase = M.toBase) : L ≃ₐ[K] F :=
  { N.ffEquiv.trans (e.hom.functionFieldRingEquivOfIsOpenImmersion.trans M.ffEquiv.symm) with
    commutes' := by
      intro a
      apply M.ffEquiv.injective
      change M.ffEquiv (M.ffEquiv.symm
        (e.hom.functionFieldRingEquivOfIsOpenImmersion (N.ffEquiv (algebraMap K L a)))) =
          M.ffEquiv (algebraMap K F a)
      rw [M.ffEquiv.apply_symm_apply, N.ffEquiv_algebraMap, M.ffEquiv_algebraMap]
      change e.hom.functionFieldMap e.hom.homeomorph.surjective.denseRange
        (baseToFunctionField N.toBase a) = _
      exact (Scheme.Hom.functionFieldMap_baseToFunctionField N.toBase e.hom
        e.hom.homeomorph.surjective.denseRange a).trans
        (congrArg (fun f : M.C ⟶ Spec (.of K) => baseToFunctionField f a) he) }

private theorem mem_placeOfPoint_iff_ffEquiv_mem_stalk_range
    (M : CurveModel K F) (x : closedPoints M.C) (z : F) :
    z ∈ (M.placeOfPoint x).toValuationSubring ↔
      M.ffEquiv z ∈ (algebraMap (M.C.presheaf.stalk x.val) M.C.functionField).range := by
  change z ∈ (M.placeOfPoint x).toValuationSubring.toSubring ↔ _
  rw [← M.range_stalk_eq x]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    change M.ffEquiv.symm (algebraMap _ M.C.functionField a) = z at ha
    simpa only [M.ffEquiv.apply_symm_apply] using congrArg M.ffEquiv ha
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    change M.ffEquiv.symm (algebraMap _ M.C.functionField a) = z
    simpa only [M.ffEquiv.symm_apply_apply] using congrArg M.ffEquiv.symm ha

/-- Pullback on places is the inverse of the actual map on closed points.
No independent field-place compatibility is assumed. -/
theorem modelIsoFieldEquiv_placeOfPoint
    (M : CurveModel K F) (N : CurveModel K L) (e : M.C ≅ N.C)
    (he : e.hom ≫ N.toBase = M.toBase) (x : closedPoints M.C) :
    Place.congrRingEquiv (modelIsoFieldEquiv M N e he).toRingEquiv
      (modelIsoFieldEquiv M N e he).commutes
      (N.placeOfPoint ((CurveModel.closedPointsEquivOfIso e).symm x)) =
        M.placeOfPoint x := by
  let φ := modelIsoFieldEquiv M N e he
  apply Place.ext
  apply SetLike.ext
  intro z
  obtain ⟨w, rfl⟩ := φ.surjective z
  rw [Place.congrRingEquiv_toValuationSubring, ValuationSubring.mem_comap]
  change φ.symm (φ w) ∈ (N.placeOfPoint
      ((CurveModel.closedPointsEquivOfIso e).symm x)).toValuationSubring ↔
    φ w ∈ (M.placeOfPoint x).toValuationSubring
  rw [φ.symm_apply_apply,
    mem_placeOfPoint_iff_ffEquiv_mem_stalk_range,
    mem_placeOfPoint_iff_ffEquiv_mem_stalk_range]
  have hφ : M.ffEquiv (φ w) =
      e.hom.functionFieldRingEquivOfIsOpenImmersion (N.ffEquiv w) :=
    M.ffEquiv.apply_symm_apply _
  rw [hφ]
  exact (e.hom.functionFieldMap_mem_stalk_range_iff_of_isOpenImmersion
    (e.hom.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace e.hom)
    x.val (N.ffEquiv w)).symm


/-- The same field equivalence is induced on the actual open charts. This
identifies the field map used in pointed inertia transport with the ambient
model map, rather than with an independently chosen field equivalence. -/
theorem modelIsoFieldEquiv_open_square
    (M : CurveModel K F) (N : CurveModel K L)
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (jX : X ⟶ M.C) (jY : Y ⟶ N.C) [IsOpenImmersion jX] [IsOpenImmersion jY]
    (hjX : DenseRange jX) (hjY : DenseRange jY)
    [Algebra F X.functionField] [Algebra L Y.functionField]
    (hfieldX : algebraMap F X.functionField =
      (jX.functionFieldMap hjX).comp M.ffEquiv.toRingHom)
    (hfieldY : algebraMap L Y.functionField =
      (jY.functionFieldMap hjY).comp N.ffEquiv.toRingHom)
    (e : M.C ≅ N.C) (he : e.hom ≫ N.toBase = M.toBase)
    (i : X ≅ Y) (hi : i.hom ≫ jY = jX ≫ e.hom) (z : L) :
    i.hom.functionFieldRingEquivOfIsOpenImmersion (algebraMap L Y.functionField z) =
      algebraMap F X.functionField (modelIsoFieldEquiv M N e he z) := by
  have heDense : DenseRange e.hom :=
    e.hom.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace e.hom
  have hiDense : DenseRange i.hom :=
    i.hom.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace i.hom
  have hmap : (i.hom.functionFieldMap hiDense).comp (jY.functionFieldMap hjY) =
      (jX.functionFieldMap hjX).comp (e.hom.functionFieldMap heDense) := by
    rw [EtaleFundamentalGroups.functionFieldMap_comp_of_dense,
      EtaleFundamentalGroups.functionFieldMap_comp_of_dense]
    congr 1
  have hφ : M.ffEquiv (modelIsoFieldEquiv M N e he z) =
      e.hom.functionFieldMap heDense (N.ffEquiv z) :=
    M.ffEquiv.apply_symm_apply _
  rw [hfieldX, hfieldY]
  change i.hom.functionFieldMap hiDense (jY.functionFieldMap hjY (N.ffEquiv z)) =
    jX.functionFieldMap hjX (M.ffEquiv (modelIsoFieldEquiv M N e he z))
  rw [hφ]
  exact DFunLike.congr_fun hmap (N.ffEquiv z)

/-- The already constructed boundary bijection retains the very same place
as the actual function-field pullback used by inertia transport. -/
theorem boundaryPlaceEquivOfModelIso_fieldPlace
    (M : CurveModel K F) (N : CurveModel K L)
    {X Y : Scheme} (jX : X ⟶ M.C) (jY : Y ⟶ N.C)
    (e : M.C ≅ N.C) (he : e.hom ≫ N.toBase = M.toBase)
    (i : X ≅ Y) (hi : i.hom ≫ jY = jX ≫ e.hom)
    (p : M.openBoundaryPlaces jX) :
    Place.congrRingEquiv (modelIsoFieldEquiv M N e he).toRingEquiv
      (modelIsoFieldEquiv M N e he).commutes
      (boundaryPlaceEquivOfModelIso M N jX jY e i hi p).val = p.val := by
  change Place.congrRingEquiv (modelIsoFieldEquiv M N e he).toRingEquiv
    (modelIsoFieldEquiv M N e he).commutes
    (N.placeOfPoint ((CurveModel.closedPointsEquivOfIso e).symm
      (M.placeEquiv.symm p.val))) = p.val
  exact (modelIsoFieldEquiv_placeOfPoint M N e he (M.placeEquiv.symm p.val)).trans
    (M.placeEquiv.apply_symm_apply p.val)

end AnabelianGeometry.WeightFiltration
