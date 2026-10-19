/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Extensions.FiniteSimpleExtensions
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveSeparatingTranscendental
import Nyll.JacobianVarieties.Kummer.OpenCurveCover
import Nyll.EtaleFundamentalGroups.Normalization.OpenNormalizationFiniteModel
import Nyll.AlgebraicCurves.Models.FunctionFields.FiniteFlatHomAlgHom
import Nyll.AlgebraicCurves.Models.Construction.BasicPerfectField
import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
import Nyll.AlgebraicCurves.Models.Ramification.OpenBoundary
import Nyll.SchemeTheory.FunctionFields.OpenChartGenericPoints
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.Noetherian

/-! # The actual proper model of an irreducible open Kummer cover

The normalized cover and its proper compactification use the same root field.
The polynomial's irreducibility supplies the field, while the interior-order
condition defining openKummerUnits supplies étaleness on the original open.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve TopologicalSpace
open scoped Polynomial

namespace AnabelianGeometry.GeometricFundamentalGroup

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

private local instance fieldSpecQuasiCompact
    {L : Type} [Field L] {S : Scheme} (g : Spec (.of L) ⟶ S) :
    QuasiCompact g where
  isCompact_preimage U _ _ := (Set.toFinite (g ⁻¹' U)).isCompact

/-- The actual irreducible root field gives a finite map of proper models
whose restriction is the original finite étale Kummer cover. -/
theorem exists_kummer_model_of_irreducible
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F)
    (U : M.C.Opens) (hU : (U : Set M.C).Nonempty)
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    (u : Pic0.openKummerUnits K F (M.openBoundaryPlaces U.ι) n)
    (hirr : Irreducible (Polynomial.X ^ (n : ℕ) - Polynomial.C (u.val : F))) :
    let P : Polynomial F := Polynomial.X ^ (n : ℕ) - Polynomial.C (u.val : F)
    let : Fact (Irreducible P) := ⟨hirr⟩
    let L := AdjoinRoot P
    let : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
    ∃ (N : CurveModel K L) (d : N.C ⟶ M.C),
      d ≫ M.toBase = N.toBase ∧ IsFinite d ∧ Flat d ∧ Surjective d ∧
      IsFiniteEtale (morphismRestrict d U) ∧ (d ⁻¹ᵁ U : Set N.C).Nonempty := by
  intro P hP L aL
  have : @IsScalarTower K F L
      (inferInstance : Algebra K F).toSMul
      (inferInstance : Algebra F L).toSMul aL.toSMul :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := F) (A := L) fun _ => rfl
  have : Nonempty U := hU.to_subtype
  have : IsIntegral U.toScheme := inferInstance
  have : IsLocallyNoetherian M.C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  have : CompactSpace M.C := QuasiCompact.compactSpace_of_compactSpace M.toBase
  have : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace U.ι
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  have : Algebra.EssFiniteType K F := by
    let : Algebra K M.C.functionField := M.functionFieldAlgebra
    have : Algebra.EssFiniteType K M.C.functionField := essFiniteType_functionField M.toBase
    exact Algebra.EssFiniteType.of_surjective M.ffAlgEquiv.symm.toAlgHom
      M.ffAlgEquiv.symm.surjective
  have : FiniteDimensional F L := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  obtain ⟨t, ht, hfinite, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have htL : Transcendental K (algebraMap F L t) :=
    (transcendental_algebraMap_iff (algebraMap F L).injective).mpr ht
  have hfiniteL : FiniteDimensional
      (IntermediateField.adjoin K ({algebraMap F L t} : Set L)) L :=
    AlgebraicCurve.finiteDimensional_adjoin_algebraMap
      (L := K) (F' := L) t hfinite
  obtain ⟨N⟩ := CurveModel.nonempty_of_perfectField K L ⟨_, htL, hfiniteL⟩
  let φ : F →ₐ[K] L := IsScalarTower.toAlgHom K F L
  have : Algebra.IsIntegral F L := Algebra.IsIntegral.of_finite F L
  have hφ : φ.toRingHom.IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  have hAlong : algebraAlong φ = (inferInstance : Algebra F L) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have hfin : FiniteAlong K φ :=
    (congrArg (fun a : Algebra F L => let : Algebra F L := a; Module.Finite F L)
      hAlong).mpr (inferInstance : Module.Finite F L)
  have hrankAlong : finrankAlong K φ = Module.finrank F L :=
    congrArg (fun a : Algebra F L => let : Algebra F L := a; Module.finrank F L) hAlong
  obtain ⟨d, hd, hdfinite, hdflat, hfp, hrank, hgeneric, _hplaces, _hunique⟩ :=
    CurveModel.exists_finite_flat_hom_of_algHom M N φ hφ hfin
  have : IsFinite d := hdfinite
  have : Flat d := hdflat
  have : LocallyOfFinitePresentation d := hfp
  have : Smooth N.toBase := SmoothOfRelativeDimension.smooth 1 N.toBase
  have : IsLocallyNoetherian N.C := LocallyOfFiniteType.isLocallyNoetherian N.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral N.C := IsNormalIntegral.of_stalks N.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk N.toBase x).2)
  let c := M.ffEquiv.trans U.ι.functionFieldRingEquivOfIsOpenImmersion
  let g : Spec (.of L) ⟶ U.toScheme :=
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ U.toScheme.functionFieldChartPoint c
  let q := N.C.functionFieldChartPoint N.ffEquiv
  have hcancel : N.ffEquiv.symm.toRingHom.comp
      (N.ffEquiv.toRingHom.comp (φ.toRingHom.comp M.ffEquiv.symm.toRingHom)) =
      φ.toRingHom.comp M.ffEquiv.symm.toRingHom := by
    ext z
    exact N.ffEquiv.symm_apply_apply _
  have hq : q ≫ d = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      M.C.functionFieldChartPoint M.ffEquiv := by
    change (Spec.map (CommRingCat.ofHom N.ffEquiv.symm.toRingHom) ≫
      N.C.fromSpecStalk (genericPoint N.C)) ≫ d = _
    rw [Category.assoc, hgeneric, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hcancel]
    change Spec.map (CommRingCat.ofHom (φ.toRingHom.comp M.ffEquiv.symm.toRingHom)) ≫ _ = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rfl
  have htriangle : q ≫ d = g ≫ U.ι := by
    rw [hq]
    dsimp only [g]
    rw [Category.assoc, Scheme.functionFieldChartPoint_comp_openImmersion]
  let η := N.C.fromSpecStalk (genericPoint N.C)
  have : IsDominant η := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro z
    apply (genericPoint_specializes z).mem_closed isClosed_closure
    exact subset_closure ⟨IsLocalRing.closedPoint N.C.functionField,
      Scheme.fromSpecStalk_closedPoint (X := N.C) (x := genericPoint N.C)⟩
  let eField := Scheme.Spec.mapIso N.ffEquiv.symm.toCommRingCatIso.op
  have : IsDominant q := by change IsDominant (eField.hom ≫ η); infer_instance
  have : IsPreimmersion q := by change IsPreimmersion (eField.hom ≫ η); infer_instance
  have hdSurj : Surjective d := (Scheme.Hom.one_le_finrank_iff_surjective d).mp (fun x => by
    rw [hrank x, hrankAlong]
    exact Module.finrank_pos)
  obtain ⟨eModel, heModel, _hModelGeneric⟩ :=
    EtaleFundamentalGroups.exists_openNormalization_iso_pullback_of_generic_field
      g U.ι d q htriangle
  have hj : DenseRange U.ι :=
    U.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace U.ι
  have hi : ∀ (y : U.toScheme) (x : closedPoints M.C),
      x.val = U.ι y → M.placeOfPoint x ∉ M.openBoundaryPlaces U.ι :=
    M.place_not_mem_openBoundaryPlaces U.ι
  let W := M.openKummerCover (M.openBoundaryPlaces U.ι) n hn u U.ι hj hi
  let Q : Polynomial U.toScheme.functionField :=
    Polynomial.X ^ (n : ℕ) - Polynomial.C (c (u.val : F))
  have hpoly : Associated (Q.map c.symm) P := by
    simpa only [Q, P, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, RingEquiv.coe_toRingHom, c.symm_apply_apply] using (Associated.refl P)
  let eRoot : AdjoinRoot Q ≃+* L := AdjoinRoot.mapRingEquiv c.symm Q P hpoly
  have hcoeff (z : U.toScheme.functionField) :
      eRoot (AdjoinRoot.of Q z) = φ (c.symm z) := by
    change AdjoinRoot.map c.symm.toRingHom Q P hpoly.symm.dvd (AdjoinRoot.of Q z) = _
    exact AdjoinRoot.map_of c.symm.toRingHom Q P hpoly.symm.dvd z
  let gA := M.openKummerGenericMap (M.openBoundaryPlaces U.ι) n u U.ι hj
  let eSource : Spec (.of (AdjoinRoot Q)) ≅ Spec (.of L) :=
    (Scheme.Spec.mapIso eRoot.toCommRingCatIso.op).symm
  have hcoeffInv : eRoot.symm.toRingHom.comp (φ.toRingHom.comp c.symm.toRingHom) =
      AdjoinRoot.of Q := by
    ext z
    apply eRoot.injective
    change eRoot (eRoot.symm (φ (c.symm z))) = _
    rw [eRoot.apply_symm_apply]
    exact (hcoeff z).symm
  have hSource : eSource.hom ≫ g = gA := by
    change Spec.map (CommRingCat.ofHom eRoot.symm.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom c.symm.toRingHom) ≫
          U.toScheme.fromSpecStalk (genericPoint U.toScheme))) =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.of Q)) ≫
        U.toScheme.fromSpecStalk (genericPoint U.toScheme)
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      RingHom.comp_assoc, hcoeffInv]
  let eNorm := EtaleFundamentalGroups.Inertia.normalizationSourceIso gA g eSource hSource
  let e : W.left ≅ pullback d U.ι := eNorm ≪≫ eModel
  have he : e.hom ≫ pullback.snd d U.ι = W.hom := by
    change (eNorm.hom ≫ eModel.hom) ≫ pullback.snd d U.ι = W.hom
    exact (Category.assoc _ _ _).trans
      ((congrArg (eNorm.hom ≫ ·) heModel).trans
        (EtaleFundamentalGroups.Inertia.normalizationSourceIso_hom_fromNormalization _ _ _ _))
  have : IsFiniteEtale W.hom := W.prop
  have hsnd : pullback.snd d U.ι = e.inv ≫ W.hom := by
    rw [← he, e.inv_hom_id_assoc]
  have : IsFiniteEtale (pullback.snd d U.ι) := by
    rw [hsnd]
    exact ⟨⟩
  let eOpen := (isPullback_morphismRestrict d U).flip.isoPullback
  have hopen : morphismRestrict d U = eOpen.hom ≫ pullback.snd d U.ι :=
    (isPullback_morphismRestrict d U).flip.isoPullback_hom_snd.symm
  have hEtale : IsFiniteEtale (morphismRestrict d U) := by
    rw [hopen]
    exact ⟨⟩
  have hV : (d ⁻¹ᵁ U : Set N.C).Nonempty := by
    obtain ⟨x, hx⟩ := hU
    obtain ⟨y, hy⟩ := hdSurj.surj x
    exact ⟨y, by change d y ∈ (U : Set M.C); rw [hy]; exact hx⟩
  exact ⟨N, d, hd, hdfinite, hdflat, hdSurj, hEtale, hV⟩

end AnabelianGeometry.GeometricFundamentalGroup
