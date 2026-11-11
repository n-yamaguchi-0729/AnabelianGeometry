/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective
public import Nyll.AnabelianGeometry.GeometricFundamentalGroup.BoundaryModelTransport
public import Nyll.SchemeTheory.FunctionFields.OpenImmersion
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality
public import Nyll.SchemeTheory.FunctionFields.ScalarFunctoriality
public import Nyll.SchemeTheory.FunctionFields.StalkFunctoriality
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FullConstants
public import Nyll.AlgebraicCurves.Places.Rational.Basic
public import Nyll.AlgebraicCurves.Places.Restriction.OrderRigidity
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # The actual place map of a specified model isomorphism

The field equivalence is the pullback of the supplied scheme isomorphism.
Its action on places agrees with the actual map on closed points, by the
stalk range formula. Thus the boundary labels transported geometrically are
exactly the labels used in function-field inertia transport.
-/

@[expose] public section

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

/-- Fixing every closed center forces a finite-field curve automorphism to
be the identity as a scheme, without any prior compatibility with constants. -/
theorem modelIso_eq_refl_of_closedCenters
    [Finite K] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FunctionField K F] (M : CurveModel K F)
    (e : M.C ≅ M.C)
    (hpoint : ∀ x : closedPoints M.C, e.hom x.val = x.val) : e = Iso.refl M.C := by
  let σ : F ≃+* F :=
    M.ffEquiv.trans (e.hom.functionFieldRingEquivOfIsOpenImmersion.trans M.ffEquiv.symm)
  have hσvalue (z : F) : M.ffEquiv (σ z) =
      e.hom.functionFieldRingEquivOfIsOpenImmersion (M.ffEquiv z) :=
    M.ffEquiv.apply_symm_apply _
  have hord (v : Place K F) (z : F) : v.ord (σ z) = v.ord z := by
    obtain ⟨x, rfl⟩ := M.placeEquiv.surjective v
    apply Place.ord_ringEquiv_of_valuationSubring (M.placeOfPoint x) σ
    intro w
    rw [mem_placeOfPoint_iff_ffEquiv_mem_stalk_range,
      mem_placeOfPoint_iff_ffEquiv_mem_stalk_range, hσvalue]
    have h := e.hom.functionFieldMap_mem_stalk_range_iff_of_isOpenImmersion
      e.hom.homeomorph.surjective.denseRange x.val (M.ffEquiv w)
    rw [hpoint x] at h
    exact h
  have hσ : σ.toRingHom = RingHom.id F :=
    FunctionField.ringHom_eq_id_of_forall_ord_eq K F σ.toRingHom hord
  have hd : DenseRange e.hom := e.hom.homeomorph.surjective.denseRange
  have hfield : e.hom.functionFieldMap hd = RingHom.id M.C.functionField := by
    apply RingHom.ext
    intro z
    apply M.ffEquiv.symm.injective
    have h := congrArg (fun f : F →+* F => f (M.ffEquiv.symm z)) hσ
    change M.ffEquiv.symm (e.hom.functionFieldMap hd
      (M.ffEquiv (M.ffEquiv.symm z))) = M.ffEquiv.symm z at h
    rw [M.ffEquiv.apply_symm_apply] at h
    exact h
  let p := M.C.fromSpecStalk (genericPoint M.C)
  have : IsDominant p := AlgebraicGeometry.FiniteEtale.genericPoint_isDominant M.C
  have : M.C.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from M.toBase]
    infer_instance⟩
  have hgeneric : p ≫ e.hom = p := by
    have h := EtaleFundamentalGroups.Spec_functionFieldMap_fromSpecStalk e.hom hd
    rw [hfield] at h
    change Spec.map (𝟙 M.C.functionField) ≫ p = p ≫ e.hom at h
    rw [Spec.map_id, Category.id_comp] at h
    exact h.symm
  apply Iso.ext
  exact ext_of_isDominant p (hgeneric.trans (Category.comp_id p).symm)

/-- The closed-center map determines an arbitrary scheme isomorphism of
finite-field curve models. In particular no common scalar automorphism is
needed when comparing two semilinear arithmetic deck composites. -/
theorem modelIso_eq_of_closedCenters
    [Finite K] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FunctionField K F] (M : CurveModel K F) (N : CurveModel K L)
    (e₁ e₂ : M.C ≅ N.C)
    (hpoint : ∀ x : closedPoints M.C, e₁.hom x.val = e₂.hom x.val) : e₁ = e₂ := by
  have h := modelIso_eq_refl_of_closedCenters M (e₁ ≪≫ e₂.symm)
    (fun x => by
      change e₂.inv (e₁.hom x.val) = x.val
      rw [hpoint]
      exact congrArg (fun f : M.C ⟶ M.C => f x.val) e₂.hom_inv_id)
  apply Iso.ext
  have hh := congrArg (fun a : M.C ≅ M.C => a.hom ≫ e₂.hom) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    e₂.inv_hom_id, Category.comp_id, Iso.refl_hom, Category.id_comp] using hh

/-- A finite-field curve-model automorphism fixing every closed center is
the identity on the scheme, including every residue-field map. -/
theorem modelIso_eq_refl_of_closedPoints
    [Finite K] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FunctionField K F] (M : CurveModel K F)
    (e : M.C ≅ M.C) (he : e.hom ≫ M.toBase = M.toBase)
    (hpoint : ∀ x : closedPoints M.C, e.hom x.val = x.val) : e = Iso.refl M.C := by
  let σ := modelIsoFieldEquiv M M e he
  have hord (v : Place K F) (z : F) : v.ord (σ z) = v.ord z := by
    obtain ⟨x, rfl⟩ := M.placeEquiv.surjective v
    have hx : (CurveModel.closedPointsEquivOfIso e).symm x = x :=
      Subtype.ext (hpoint x)
    have hp := modelIsoFieldEquiv_placeOfPoint M M e he x
    rw [hx] at hp
    have ho := Place.ord_congrRingEquiv σ.toRingEquiv σ.commutes (M.placeOfPoint x) z
    rw [hp] at ho
    simpa only [M.placeEquiv_apply, AlgEquiv.coe_toRingEquiv] using ho
  have hσ : σ.toRingHom = RingHom.id F :=
    FunctionField.ringHom_eq_id_of_forall_ord_eq K F σ.toRingHom hord
  have hd : DenseRange e.hom := e.hom.homeomorph.surjective.denseRange
  have hfield : e.hom.functionFieldMap hd = RingHom.id M.C.functionField := by
    apply RingHom.ext
    intro z
    apply M.ffEquiv.symm.injective
    have h := congrArg (fun f : F →+* F => f (M.ffEquiv.symm z)) hσ
    change M.ffEquiv.symm (e.hom.functionFieldMap hd
      (M.ffEquiv (M.ffEquiv.symm z))) = M.ffEquiv.symm z at h
    rw [M.ffEquiv.apply_symm_apply] at h
    exact h
  let p := M.C.fromSpecStalk (genericPoint M.C)
  have : IsDominant p := AlgebraicGeometry.FiniteEtale.genericPoint_isDominant M.C
  have hgeneric : p ≫ e.hom = p := by
    have h := EtaleFundamentalGroups.Spec_functionFieldMap_fromSpecStalk e.hom hd
    rw [hfield] at h
    change Spec.map (𝟙 M.C.functionField) ≫ p = p ≫ e.hom at h
    rw [Spec.map_id, Category.id_comp] at h
    exact h.symm
  apply Iso.ext
  apply ext_of_isDominant_of_isSeparated M.toBase
    (he.trans (Category.id_comp _).symm) p
  exact hgeneric.trans (Category.comp_id p).symm

/-- Isomorphisms with the same scalar automorphism are determined by their
closed-center maps. Composing one with the inverse of the other yields an
actual automorphism over the original finite field. -/
theorem modelIso_eq_of_closedPoints_of_common_semilinearity
    [Finite K] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FunctionField K F] (M : CurveModel K F) (N : CurveModel K L)
    (e₁ e₂ : M.C ≅ N.C) (τ : K ≃+* K)
    (he₁ : e₁.hom ≫ N.toBase ≫ Spec.map (CommRingCat.ofHom τ.toRingHom) = M.toBase)
    (he₂ : e₂.hom ≫ N.toBase ≫ Spec.map (CommRingCat.ofHom τ.toRingHom) = M.toBase)
    (hpoint : ∀ x : closedPoints M.C, e₁.hom x.val = e₂.hom x.val) : e₁ = e₂ := by
  have hInv : e₂.inv ≫ M.toBase =
      N.toBase ≫ Spec.map (CommRingCat.ofHom τ.toRingHom) := by
    rw [← he₂, e₂.inv_hom_id_assoc]
  have h := modelIso_eq_refl_of_closedPoints M (e₁ ≪≫ e₂.symm)
    (by change (e₁.hom ≫ e₂.inv) ≫ M.toBase = M.toBase
        rw [Category.assoc, hInv, he₁])
    (fun x => by
      change e₂.inv (e₁.hom x.val) = x.val
      rw [hpoint]
      exact congrArg (fun f : M.C ⟶ M.C => f x.val) e₂.hom_inv_id)
  apply Iso.ext
  have hh := congrArg (fun a : M.C ≅ M.C => a.hom ≫ e₂.hom) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    e₂.inv_hom_id, Category.comp_id, Iso.refl_hom, Category.id_comp] using hh

/-- For actual finite-field curve-model isomorphisms over the same field,
equality on closed centers is equality of the full scheme isomorphisms. -/
theorem modelIso_eq_of_closedPoints
    [Finite K] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FunctionField K F] (M : CurveModel K F) (N : CurveModel K L)
    (e₁ e₂ : M.C ≅ N.C)
    (he₁ : e₁.hom ≫ N.toBase = M.toBase) (he₂ : e₂.hom ≫ N.toBase = M.toBase)
    (hpoint : ∀ x : closedPoints M.C, e₁.hom x.val = e₂.hom x.val) : e₁ = e₂ := by
  have hid : Spec.map (CommRingCat.ofHom (RingEquiv.refl K).toRingHom) =
      𝟙 (Spec (.of K)) := Spec.map_id _
  exact modelIso_eq_of_closedPoints_of_common_semilinearity M N e₁ e₂ (RingEquiv.refl K)
    (by rw [hid, Category.comp_id]; exact he₁)
    (by rw [hid, Category.comp_id]; exact he₂) hpoint

end AnabelianGeometry.WeightFiltration
