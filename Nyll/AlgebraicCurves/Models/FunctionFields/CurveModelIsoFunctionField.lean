/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_exists_iso_comp_toBase_eq_placeOfPoint_congr_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Models.Points.IsoCompToBaseEqPlaceOfPointCongrEq
public import Nyll.AlgebraicCurves.Geometry.Schemes.FunctionFields.OpenImmersionFunctionFieldIso
public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.IsoCompEqOpenImmersion
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality

/-! # A model isomorphism retaining its prescribed function-field map

The generic-point equation in the actual smooth-proper extension construction
is retained. This permits subsequent normalized Kummer charts to use the same
pair function, rather than only an unspecified projective-line isomorphism.
-/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open AlgebraicCurves.Models.Proofs
open CurveModel_exists_iso_comp_toBase_eq_placeOfPoint_congr_eq.AlgebraicCurve

namespace AlgebraicGeometry.Scheme

universe u

/-- The original smooth-proper extension construction retains the specified
isomorphism of function fields and its generic-point equation. -/
theorem exists_iso_functionFieldMap_eq
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    (cX : X ⟶ Spec (.of K)) (cY : Y ⟶ Spec (.of K))
    [IsProper cX] [SmoothOfRelativeDimension 1 cX]
    [IsProper cY] [Smooth cY]
    (ψ : X.functionField ≅ Y.functionField)
    (hψ : Spec.map ψ.inv ≫ Y.fromSpecStalk (genericPoint Y) ≫ cY =
      X.fromSpecStalk (genericPoint X) ≫ cX) :
    ∃ e : X ≅ Y, e.hom ≫ cY = cX ∧
      (X.fromSpecStalk (genericPoint X) ≫ e.hom =
        Spec.map ψ.inv ≫ Y.fromSpecStalk (genericPoint Y)) ∧
      ∀ hdense : DenseRange e.hom,
        CommRingCat.ofHom (e.hom.functionFieldMap hdense) = ψ.inv := by
  obtain ⟨U, hη, j, himm, hj, hjη⟩ :=
    exists_isOpenImmersion_of_functionField_iso cX cY ψ hψ
  obtain ⟨e, he, heU⟩ :=
    exists_iso_comp_eq_of_isOpenImmersion_of_isProper cX cY
      U ⟨genericPoint X, hη⟩ j hj
  have hgen : X.fromSpecStalk (genericPoint X) ≫ e.hom =
      Spec.map ψ.inv ≫ Y.fromSpecStalk (genericPoint Y) := by
    rw [← Scheme.Opens.fromSpecStalkOfMem_ι U (genericPoint X) hη,
      Category.assoc, heU, hjη]
  refine ⟨e, he, hgen, fun hdense => ?_⟩
  apply Spec.map_injective
  apply (cancel_mono (Y.fromSpecStalk (genericPoint Y))).mp
  exact (EtaleFundamentalGroups.Spec_functionFieldMap_fromSpecStalk e.hom hdense).trans hgen

end AlgebraicGeometry.Scheme

namespace AlgebraicCurve.CurveModel

universe u v w

/-- The actual model isomorphism realizes the prescribed inverse field map. -/
theorem exists_iso_comp_toBase_eq_functionFieldMap_eq
    {K : Type u} [Field K]
    {F : Type v} [Field F] [Algebra K F] {F' : Type w} [Field F'] [Algebra K F']
    (φ : F ≃ₐ[K] F') (M : CurveModel K F) (M' : CurveModel K F') :
    ∃ e : M.C ≅ M'.C, e.hom ≫ M'.toBase = M.toBase ∧
      ∀ (hdense : DenseRange e.hom) (z : F'),
        e.hom.functionFieldMap hdense (M'.ffEquiv z) = M.ffEquiv (φ.symm z) := by
  let ψr : M.C.functionField ≃+* M'.C.functionField :=
    M.ffEquiv.symm.trans (φ.toRingEquiv.trans M'.ffEquiv)
  let ψ : M.C.functionField ≅ M'.C.functionField := ψr.toCommRingCatIso
  have hψinv : ∀ z, ψ.inv.hom z = M.ffEquiv (φ.symm (M'.ffEquiv.symm z)) := fun z => rfl
  have hb : CommRingCat.ofHom (baseToFunctionField M'.toBase) ≫ ψ.inv =
      CommRingCat.ofHom (baseToFunctionField M.toBase) := by
    ext a
    change ψ.inv.hom (baseToFunctionField M'.toBase a) = baseToFunctionField M.toBase a
    rw [hψinv, ← M'.ffEquiv_algebraMap a, RingEquiv.symm_apply_apply,
      show φ.symm (algebraMap K F' a) = algebraMap K F a from φ.symm.commutes a,
      M.ffEquiv_algebraMap]
  have hψ : Spec.map ψ.inv ≫ M'.C.fromSpecStalk (genericPoint M'.C) ≫ M'.toBase =
      M.C.fromSpecStalk (genericPoint M.C) ≫ M.toBase := by
    rw [fromSpecStalk_genericPoint_comp_toBase,
      fromSpecStalk_genericPoint_comp_toBase,
      ← Spec.map_comp, hb]
  have : Smooth M'.toBase :=
    SmoothOfRelativeDimension.smooth (n := 1) (f := M'.toBase)
  obtain ⟨e, he, -, hfield⟩ :=
    AlgebraicGeometry.Scheme.exists_iso_functionFieldMap_eq
      M.toBase M'.toBase ψ hψ
  refine ⟨e, he, fun hdense z => ?_⟩
  have hmap := congrArg (fun q : M'.C.functionField ⟶ M.C.functionField =>
    q.hom (M'.ffEquiv z)) (hfield hdense)
  exact hmap.trans (by rw [hψinv, RingEquiv.symm_apply_apply])

end AlgebraicCurve.CurveModel
