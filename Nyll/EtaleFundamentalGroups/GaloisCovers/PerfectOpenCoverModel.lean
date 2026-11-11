/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverModelIso
public import Nyll.EtaleFundamentalGroups.GeometricFiber.RecoveredCoverGeometricIntegrality
public import Nyll.SchemeTheory.LocalGeometry.IntegralSmooth

/-!
# Actual covering compactifications over any perfect field

The original finite-cover function field has a smooth proper model over a
perfect field, including finite fields. The same finite map and normalization
comparison retain the original base morphism and generic embedding.

This generalizes the characteristic-zero supplier in `OpenCoverFiniteModel`
and `OpenCoverModelIso`; its proofs reuse their existing characteristic-free
constructions. At integration, the old characteristic-zero statements become
specializations of this perfect-field version.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open CategoryTheory.PreGaloisCategory
open AlgebraicCurves.Models.Proofs.IsCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one

namespace EtaleFundamentalGroups

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The function field of a connected finite étale open cover has a smooth
proper model whose finite map extends the original generic morphism. -/
theorem exists_finite_curveModel_map_of_open_cover_of_perfectField
    {K : Type uGeom} {F : Type uField₁} [Field K] [PerfectField K]
    [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme.{uGeom}} [IsIntegral X] [IsNormalIntegral X]
    (j : X ⟶ M.C) [IsOpenImmersion j]
    (W : FiniteEtale X) [IsConnected W] :
    let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let cW : W.left ⟶ Spec (.of K) := W.hom ≫ j ≫ M.toBase
    let : Algebra K W.left.functionField := (baseToFunctionField cW).toAlgebra
    ∃ (N : CurveModel K W.left.functionField) (d : N.C ⟶ M.C),
      d ≫ M.toBase = N.toBase ∧ IsFinite d ∧
      (Spec.map (CommRingCat.ofHom N.ffEquiv.symm.toRingHom) ≫
        N.C.fromSpecStalk (genericPoint N.C)) ≫ d =
          W.left.fromSpecStalk (genericPoint W.left) ≫ W.hom ≫ j := by
  intro hWIntegral cW algW
  have : IsIntegral ((Functor.id Scheme.{uGeom}).obj W.left) := hWIntegral
  have : IsIntegral ((Functor.fromPUnit X).obj W.right) :=
    inferInstanceAs (IsIntegral X)
  have : IsFiniteEtale W.hom := W.prop
  have : SmoothOfRelativeDimension 1 (j ≫ M.toBase) :=
    smoothOfRelativeDimension_comp 0 1 j M.toBase
  have : SmoothOfRelativeDimension 1 cW :=
    smoothOfRelativeDimension_comp 0 1 W.hom (j ≫ M.toBase)
  have : IsCurveOver K W.left.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one (C := W.left) cW
      (RingEquiv.refl _) (fun _ => rfl)
  have : Algebra.EssFiniteType K W.left.functionField :=
    (SmoothModelFunctionField.stageA (C := W.left) cW).1
  obtain ⟨t, ht, hfinite, _⟩ :=
    (isCurveOver_iff_exists_transcendental_finiteDimensional
      (K := K) (F := W.left.functionField)).mp inferInstance
  obtain ⟨N⟩ := CurveModel.nonempty_of_perfectField K W.left.functionField
    ⟨t, ht, hfinite⟩
  let hj : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  let hw : DenseRange W.hom := finiteEtale_hom_denseRange_of_isConnected W
  let E := M.ffEquiv.trans j.functionFieldRingEquivOfIsOpenImmersion
  let : Algebra K X.functionField := (baseToFunctionField (j ≫ M.toBase)).toAlgebra
  let e : F ≃ₐ[K] X.functionField :=
    AlgEquiv.ofRingEquiv (f := E) (M.openFunctionFieldEquiv_algebraMap j)
  let φ : F →ₐ[K] W.left.functionField :=
    (Scheme.Hom.functionFieldAlgHomOver (X := X) (Y := W.left)
      (j ≫ M.toBase) W.hom hw).comp e.toAlgHom
  let : Algebra X.functionField W.left.functionField :=
    finiteEtaleFunctionFieldAlgebra W
  have : FiniteDimensional X.functionField W.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : Algebra F W.left.functionField := algebraAlong φ
  have hcompat :
      (algebraMap F W.left.functionField).comp E.symm.toRingHom =
        (RingEquiv.refl W.left.functionField).toRingHom.comp
          (algebraMap X.functionField W.left.functionField) := by
    ext a
    change W.hom.functionFieldMap hw (E (E.symm a)) = W.hom.functionFieldMap hw a
    rw [E.apply_symm_apply]
  have hfin : FiniteAlong K φ :=
    Module.Finite.of_equiv_equiv E.symm (RingEquiv.refl W.left.functionField) hcompat
  have : FiniteDimensional F W.left.functionField := hfin
  have hφ : φ.toRingHom.IsIntegral := fun a =>
    Algebra.IsIntegral.isIntegral (R := F) a
  obtain ⟨d, hd, hdfinite, _, _, _, hgeneric, _, _⟩ :=
    M.exists_finite_flat_hom_of_algHom N φ hφ hfin
  refine ⟨N, d, hd, hdfinite, ?_⟩
  have hmap : φ.toRingHom.comp M.ffEquiv.symm.toRingHom =
      (W.hom.functionFieldMap hw).comp (j.functionFieldMap hj) := by
    ext a
    change W.hom.functionFieldMap hw
      (j.functionFieldMap hj (M.ffEquiv (M.ffEquiv.symm a))) = _
    rw [M.ffEquiv.apply_symm_apply]
    rfl
  rw [Category.assoc, hgeneric, ← Category.assoc, ← Spec.map_comp]
  have hcancel :
      CommRingCat.ofHom (N.ffEquiv.toRingHom.comp
        (φ.toRingHom.comp M.ffEquiv.symm.toRingHom)) ≫
        CommRingCat.ofHom N.ffEquiv.symm.toRingHom =
      CommRingCat.ofHom ((W.hom.functionFieldMap hw).comp (j.functionFieldMap hj)) := by
    apply CommRingCat.hom_ext
    ext a
    change N.ffEquiv.symm (N.ffEquiv (φ (M.ffEquiv.symm a))) = _
    rw [N.ffEquiv.symm_apply_apply]
    exact DFunLike.congr_fun hmap a
  rw [hcancel]
  change Spec.map (CommRingCat.ofHom (j.functionFieldMap hj) ≫
    CommRingCat.ofHom (W.hom.functionFieldMap hw)) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, Spec_functionFieldMap_fromSpecStalk j hj,
    ← Category.assoc, Spec_functionFieldMap_fromSpecStalk (X := X) (Y := W.left) W.hom hw,
    Category.assoc]

private theorem transport_normalization_model
    {A B N : Scheme.{uGeom}} (g q : A ⟶ B)
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact q] [QuasiSeparated q]
    (h : g = q) (d : N ⟶ B) (p : A ⟶ N)
    (e : g.normalization ≅ N)
    (he : e.hom ≫ d = g.fromNormalization)
    (hep : g.toNormalization ≫ e.hom = p) :
    ∃ e' : q.normalization ≅ N, e'.hom ≫ d = q.fromNormalization ∧
      q.toNormalization ≫ e'.hom = p := by
  subst q
  exact ⟨e, he, hep⟩

/-- The actual proper normalization has a smooth proper curve-model
identification over the original base, not just a function-field equivalence. -/
theorem exists_curveModel_iso_open_cover_normalization_with_generic_of_perfectField
    {K : Type uGeom} {F : Type uField₁} [Field K] [PerfectField K]
    [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme.{uGeom}}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (W : FiniteEtale X) [IsConnected W] :
    let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let cW : W.left ⟶ Spec (.of K) := W.hom ≫ j ≫ M.toBase
    let : Algebra K W.left.functionField := (baseToFunctionField cW).toAlgebra
    ∃ (N : CurveModel K W.left.functionField) (d : N.C ⟶ M.C),
      d ≫ M.toBase = N.toBase ∧ IsFinite d ∧
      ∃ e : (FiniteEtale.connectedCoverGenericComposite W ≫ j).normalization ≅ N.C,
        e.hom ≫ d = (FiniteEtale.connectedCoverGenericComposite W ≫ j).fromNormalization ∧
        (FiniteEtale.connectedCoverGenericComposite W ≫ j).toNormalization ≫ e.hom =
          Spec.map (CommRingCat.ofHom N.ffEquiv.symm.toRingHom) ≫
            N.C.fromSpecStalk (genericPoint N.C) := by
  intro hIntegral cW algW
  obtain ⟨N, d, hd, hfinite, hgeneric⟩ :=
    exists_finite_curveModel_map_of_open_cover_of_perfectField M j W
  have : IsFinite d := hfinite
  have : Smooth N.toBase := SmoothOfRelativeDimension.smooth 1 N.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral N.C := IsNormalIntegral.of_stalks N.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk N.toBase x).2)
  let eF := Scheme.Spec.mapIso N.ffEquiv.symm.toCommRingCatIso.op
  let η := N.C.fromSpecStalk (genericPoint N.C)
  have : IsDominant η := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro z
    apply (genericPoint_specializes z).mem_closed isClosed_closure
    exact subset_closure ⟨IsLocalRing.closedPoint N.C.functionField,
      Scheme.fromSpecStalk_closedPoint (X := N.C) (x := genericPoint N.C)⟩
  let p : Spec (.of W.left.functionField) ⟶ N.C := eF.hom ≫ η
  have : IsDominant p := by dsimp only [p]; infer_instance
  have : IsPreimmersion p := by dsimp only [p, η]; infer_instance
  have hid : CommRingCat.ofHom
      (algebraMap W.left.functionField W.left.functionField) = 𝟙 _ := rfl
  have hp : p ≫ d = FiniteEtale.connectedCoverGenericComposite W ≫ j := by
    change (Spec.map (CommRingCat.ofHom N.ffEquiv.symm.toRingHom) ≫
      N.C.fromSpecStalk (genericPoint N.C)) ≫ d = _
    simpa only [FiniteEtale.connectedCoverGenericComposite,
      FiniteEtale.connectedCoverGenericMorphism, Scheme.genericExtensionMorphism,
      hid, Spec.map_id, Category.id_comp, Category.assoc] using hgeneric
  obtain ⟨e, he, hep⟩ := transport_normalization_model (p ≫ d)
    (FiniteEtale.connectedCoverGenericComposite W ≫ j) hp d p
    (finiteNormalFieldSourceIso d p)
    (finiteNormalFieldSourceIso_hom_fromNormalization d p)
    (toNormalization_finiteNormalFieldSourceIso_hom d p)
  exact ⟨N, d, hd, hfinite, e, he, hep⟩

/-- The actual finite-cover compactification is smooth of relative dimension
one over the original perfect field, including positive characteristic. -/
theorem connectedCoverCompactification_smooth_of_perfectField
    {K : Type uGeom} {F : Type uField₁} [Field K] [PerfectField K] [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme.{uGeom}}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (W : FiniteEtale X) [IsConnected W] :
    SmoothOfRelativeDimension 1
      ((FiniteEtale.connectedCoverGenericComposite W ≫ j).fromNormalization ≫ M.toBase) := by
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let cW : W.left ⟶ Spec (.of K) := W.hom ≫ j ≫ M.toBase
  let : Algebra K W.left.functionField := (baseToFunctionField cW).toAlgebra
  obtain ⟨N, d, hd, _, e, he, _⟩ :=
    exists_curveModel_iso_open_cover_normalization_with_generic_of_perfectField M j W
  have h : (FiniteEtale.connectedCoverGenericComposite W ≫ j).fromNormalization ≫ M.toBase =
      e.hom ≫ N.toBase := by
    rw [← he, Category.assoc, hd]
  rw [h]
  exact smoothOfRelativeDimension_comp 0 1 e.hom N.toBase

/-- Geometric connectedness of the original smooth cover gives geometric
integrality of its actual compactification. This uses its original dense open
immersion and the displayed constant extension, without choosing a new cover. -/
theorem connectedCoverCompactification_geometricallyIntegral_of_perfectField
    {K L : Type uGeom} {F : Type uField₁} [Field K] [PerfectField K] [Field F] [Algebra K F]
    [Field L] [IsAlgClosed L] [Algebra K L]
    (M : CurveModel K F) {X : Scheme.{uGeom}}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (W : FiniteEtale X) [IsConnected W]
    [ConnectedSpace ↥(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (W.hom ≫ j ≫ M.toBase))] :
    GeometricallyIntegral
      ((FiniteEtale.connectedCoverGenericComposite W ≫ j).fromNormalization ≫ M.toBase) := by
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let cW : W.left ⟶ Spec (.of K) := W.hom ≫ j ≫ M.toBase
  let : Algebra K W.left.functionField := (baseToFunctionField cW).toAlgebra
  have : IsFiniteEtale W.hom := W.prop
  have : SmoothOfRelativeDimension 1 (j ≫ M.toBase) :=
    smoothOfRelativeDimension_comp 0 1 j M.toBase
  have : SmoothOfRelativeDimension 1 cW :=
    smoothOfRelativeDimension_comp 0 1 W.hom (j ≫ M.toBase)
  have : Smooth cW := SmoothOfRelativeDimension.smooth 1 cW
  let b := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have : IsIntegral (Limits.pullback b cW : Scheme.{uGeom}) :=
    isIntegral_of_smooth_of_preconnectedSpace (Limits.pullback.fst b cW)
  obtain ⟨N, d, _, _, e, _, _⟩ :=
    exists_curveModel_iso_open_cover_normalization_with_generic_of_perfectField M j W
  let C := (FiniteEtale.connectedCoverGenericComposite W ≫ j).normalization
  have : IsIntegral C := IsIntegral.of_isIso e.inv
  let i : W.left ⟶ C := FiniteEtale.connectedCoverCompactificationInclusion j W
  have : QuasiCompact i := by
    dsimp only [i, FiniteEtale.connectedCoverCompactificationInclusion]
    infer_instance
  have hi : DenseRange i :=
    i.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace i
  apply geometricallyIntegral_compactification_of_recovered_cover (κ := L)
    cW (Iso.refl (Limits.pullback b cW)) _ i hi
  change i ≫ (FiniteEtale.connectedCoverGenericComposite W ≫ j).fromNormalization ≫
    M.toBase = W.hom ≫ j ≫ M.toBase
  rw [← Category.assoc, FiniteEtale.connectedCoverCompactificationInclusion_comp,
    Category.assoc]

end EtaleFundamentalGroups
