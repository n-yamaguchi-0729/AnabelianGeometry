/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.KummerTheory.RatFuncPairSquareRootChart
import Nyll.EtaleFundamentalGroups.Normalization.OpenNormalizationFiniteModel
import Nyll.JacobianVarieties.Kummer.OpenCurveCover
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineRatFuncModel
import Nyll.SchemeTheory.FunctionFields.OpenChartGenericPoints
import Nyll.AlgebraicCurves.Models.FunctionFields.FiniteFlatHomAlgHom

/-! # The named rational square cover is the actual square-model open

The original normalization defining openKummerCover is identified with the
inverse image of the original open under a finite map between literal P1 models.
The generic comparison retains the original quotient root as X, so future cusp
labels refer to this same cover and this same rational coordinate.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve TopologicalSpace
open AlgebraicGeometry.ProjSpace
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
attribute [local instance] CurveModel.isIntegral CurveModel.smooth

namespace AnabelianGeometry.KummerTheory

private local instance fieldSpecQuasiCompact
    {L : Type} [Field L] {S : Scheme} (g : Spec (.of L) ⟶ S) :
    QuasiCompact g where
  isCompact_preimage U _ _ := (Set.toFinite (g ⁻¹' U)).isCompact

/-- Identify the given named square cover, preserving its actual generic root.
The coordinate eF and the function u are supplied unchanged by the caller. -/
theorem namedRationalSquareCover_exists_modelOpen
    {k : Type} [Field k]
    {U : Scheme} [IsIntegral U] [CompactSpace U]
    (j : U ⟶ (projectiveLineRatFuncModel k).C)
    [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j] (hj : DenseRange j)
    (S : Set (Place k (RatFunc k)))
    (u : Pic0.openKummerUnits k (RatFunc k) S (2 : ℕ+))
    (hi : ∀ (y : U) (x : closedPoints (projectiveLineRatFuncModel k).C),
      x.val = j y → (projectiveLineRatFuncModel k).placeOfPoint x ∉ S)
    (hn : IsUnit ((2 : ℕ) : k))
    (eF : RatFunc k ≃ₐ[k] RatFunc k) (hf : eF RatFunc.X = (u.val : RatFunc k))
    (v : Place k (RatFunc k)) (hv : v.ord (u.val : RatFunc k) = -1) :
    let M := projectiveLineRatFuncModel k
    let c := M.ffEquiv.trans j.functionFieldRingEquivOfIsOpenImmersion
    let A := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (c (u.val : RatFunc k)))
    let W := M.openKummerCover S (2 : ℕ+) hn u j hj hi
    let g := M.openKummerGenericMap S (2 : ℕ+) u j hj
    ∃ eRoot : A ≃+* RatFunc k,
      eRoot (AdjoinRoot.root (Polynomial.X ^ 2 -
        Polynomial.C (c (u.val : RatFunc k)))) = RatFunc.X ∧
      (∀ z : U.functionField, eRoot (AdjoinRoot.of
        (Polynomial.X ^ 2 - Polynomial.C (c (u.val : RatFunc k))) z) =
          ratFuncPairSquareHom eF (c.symm z)) ∧
      ∃ p : M.C ⟶ M.C,
        p ≫ M.toBase = M.toBase ∧ IsFinite p ∧ Flat p ∧
        LocallyOfFinitePresentation p ∧
        (M.C.fromSpecStalk (genericPoint M.C) ≫ p =
          Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp
            ((ratFuncPairSquareHom eF).toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
              M.C.fromSpecStalk (genericPoint M.C)) ∧
        (∀ y : closedPoints M.C, ∃ hy : p.base y.val ∈ closedPoints M.C,
          M.placeOfPoint ⟨p.base y.val, hy⟩ =
            (M.placeOfPoint y).restrictAlong (ratFuncPairSquareHom eF)
              (ratFuncPairSquareHom_isIntegral eF)) ∧
        ∃ E : W.left ≅ pullback p j,
          E.hom ≫ pullback.snd p j = W.hom ∧
          g.toNormalization ≫ E.hom ≫ pullback.fst p j =
            Spec.map (CommRingCat.ofHom eRoot.symm.toRingHom) ≫
              M.C.functionFieldChartPoint M.ffEquiv := by
  intro M c A W g
  obtain ⟨eRoot, hroot, hcoeff⟩ :=
    ratFuncPairSquare_exists_rootCoordinate_over_chart c eF (u.val : RatFunc k) hf v hv
  obtain ⟨p, hp, hfinite, hflat, hfp, _hrank, hgeneric, hplaces, _hunique⟩ :=
    CurveModel.exists_finite_flat_hom_of_algHom M M (ratFuncPairSquareHom eF)
      (ratFuncPairSquareHom_isIntegral eF) (ratFuncPairSquareHom_finite eF)
  let : IsFinite p := hfinite
  let φ := ratFuncPairSquareHom eF
  let q := M.C.functionFieldChartPoint M.ffEquiv
  let gU : Spec (.of (RatFunc k)) ⟶ U :=
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ U.functionFieldChartPoint c
  let η := M.C.fromSpecStalk (genericPoint M.C)
  have hcancel : M.ffEquiv.symm.toRingHom.comp
      (M.ffEquiv.toRingHom.comp (φ.toRingHom.comp M.ffEquiv.symm.toRingHom)) =
      φ.toRingHom.comp M.ffEquiv.symm.toRingHom := by
    ext z
    exact M.ffEquiv.symm_apply_apply _
  have hq : q ≫ p = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ q := by
    calc
      q ≫ p = Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp
            (φ.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫ η) := by
        change (Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫ η) ≫ p = _
        rw [Category.assoc, hgeneric]
      _ = Spec.map (CommRingCat.ofHom
          (φ.toRingHom.comp M.ffEquiv.symm.toRingHom)) ≫ η := by
        rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcancel]
      _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ q := by
        change _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫ η)
        rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hproper : q ≫ p = gU ≫ j := by
    rw [hq]
    dsimp only [gU]
    rw [Category.assoc, Scheme.functionFieldChartPoint_comp_openImmersion]
  have hη : IsDominant η := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro z
    apply (genericPoint_specializes z).mem_closed isClosed_closure
    exact subset_closure ⟨IsLocalRing.closedPoint M.C.functionField,
      Scheme.fromSpecStalk_closedPoint (X := M.C) (x := genericPoint M.C)⟩
  let : IsDominant η := hη
  let eqF := Scheme.Spec.mapIso M.ffEquiv.symm.toCommRingCatIso.op
  let : IsDominant q := by
    change IsDominant (eqF.hom ≫ η)
    infer_instance
  let : IsPreimmersion q := by
    change IsPreimmersion (eqF.hom ≫ η)
    infer_instance
  let : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  let : IsIntegrallyClosed Γ(Spec (.of k), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  let : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase x).2)
  obtain ⟨Efield, hEfield, hEgeneric⟩ :=
    EtaleFundamentalGroups.exists_openNormalization_iso_pullback_of_generic_field
      gU j p q hproper
  let gA : Spec (.of A) ⟶ U := g
  let eSource : Spec (.of A) ≅ Spec (.of (RatFunc k)) :=
    (Scheme.Spec.mapIso eRoot.toCommRingCatIso.op).symm
  have hcoef : eRoot.symm.toRingHom.comp (φ.toRingHom.comp c.symm.toRingHom) =
      AdjoinRoot.of (Polynomial.X ^ 2 - Polynomial.C (c (u.val : RatFunc k))) := by
    ext z
    apply eRoot.injective
    change eRoot (eRoot.symm (φ (c.symm z))) = _
    rw [eRoot.apply_symm_apply]
    exact (hcoeff z).symm
  have hSource : eSource.hom ≫ gU = gA := by
    change Spec.map (CommRingCat.ofHom eRoot.symm.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom c.symm.toRingHom) ≫
          U.fromSpecStalk (genericPoint U))) =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.of
        (Polynomial.X ^ 2 - Polynomial.C (c (u.val : RatFunc k))))) ≫
          U.fromSpecStalk (genericPoint U)
    simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcoef]; rfl
  let eNorm := EtaleFundamentalGroups.Inertia.normalizationSourceIso
    gA gU eSource hSource
  have hNorm : gA.toNormalization ≫ eNorm.hom = eSource.hom ≫ gU.toNormalization :=
    EtaleFundamentalGroups.Inertia.toNormalization_normalizationSourceIso_hom
      gA gU eSource hSource
  refine ⟨eRoot, hroot, hcoeff, p, hp, hfinite, hflat, hfp,
    hgeneric, hplaces, eNorm ≪≫ Efield, ?_, ?_⟩
  · change (eNorm ≪≫ Efield).hom ≫ pullback.snd p j = gA.fromNormalization
    rw [Iso.trans_hom, Category.assoc, hEfield]
    exact EtaleFundamentalGroups.Inertia.normalizationSourceIso_hom_fromNormalization _ _ _ _
  · change gA.toNormalization ≫ (eNorm ≪≫ Efield).hom ≫ pullback.fst p j =
      eSource.hom ≫ q
    calc
      gA.toNormalization ≫ (eNorm ≪≫ Efield).hom ≫ pullback.fst p j =
          (gA.toNormalization ≫ eNorm.hom) ≫ (Efield.hom ≫ pullback.fst p j) := by
        simp only [Iso.trans_hom, Category.assoc]
      _ = (eSource.hom ≫ gU.toNormalization) ≫ (Efield.hom ≫ pullback.fst p j) :=
        congrArg (fun a => a ≫ (Efield.hom ≫ pullback.fst p j)) hNorm
      _ = eSource.hom ≫ q := by
        rw [Category.assoc, hEgeneric]

end AnabelianGeometry.KummerTheory
