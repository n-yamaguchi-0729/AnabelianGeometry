/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Inertia.GenericPlaceInertiaHom
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisNaturality
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
import Nyll.SchemeTheory.FunctionFields.OpenChartGenericPoints
import Nyll.EtaleFundamentalGroups.GeometricFiber.MatchedFiberCoverGroupTransport
import Nyll.EtaleFundamentalGroups.Inertia.ConnectedCoverActualInertia

/-! # Actual named-model generic points and their pointed inertia images

-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve
open AlgebraicGeometry.FiniteEtale SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration
attribute [local instance] normalizationCommAlgGaloisAction

private theorem namedModel_pointedHom_equality_conjugation
    {X Y : Scheme} {Ω : Type} [Field Ω]
    (f : Y ⟶ X) (y : Spec (.of Ω) ⟶ Y) (x : Spec (.of Ω) ⟶ X)
    (h : y ≫ f = x) (a : π₁ᵉᵗ(y)) :
    pointedFundamentalGroupHom f y x h a =
      continuousConjAut (eqToIso (congrArg fiber h)) (fundamentalGroupHom f y a) := by
  subst x
  rfl

/-- The same original place inertia after an actual scheme morphism, expressed
at its prescribed target field chart. Naturality derives the inertia image;
no inertia-preservation or independently chosen point is assumed. -/
theorem genericPlaceInertia_pointed_morphism_chart_image
    {k F : Type} [Field k] [Field F] [Algebra k F]
    (Y Z : Scheme) [IsIntegral Y] [IsIntegral Z]
    (f : Y ⟶ Z) [Algebra F Y.functionField]
    {Ω : Type} [Field Ω] [Algebra Y.functionField Ω] [Algebra F Ω]
    [IsScalarTower F Y.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure Y.functionField Ω] [IsSepClosure F Ω]
    (p : Place k F) [Algebra p.toValuationSubring Ω]
    [IsScalarTower p.toValuationSubring F Ω]
    (Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω))
    (hsurj : Function.Surjective (algebraMap F Y.functionField))
    (jF : Spec (.of F) ⟶ Z)
    (hpoint : (ξ Y.functionField Ω ≫ Y.fromSpecStalk (genericPoint Y)) ≫ f =
      ξ F Ω ≫ jF) :
    let xi := ξ Y.functionField Ω ≫ Y.fromSpecStalk (genericPoint Y)
    let i := (pointedFundamentalGroupHom f xi (ξ F Ω ≫ jF) hpoint).toMonoidHom
    (genericPlaceInertia Y p Q).map i =
      (Q.inertia Gal(Ω/F)).map (fieldSourceAbsoluteGaloisHom F Ω jF).toMonoidHom := by
  intro xi i
  let e := AlgEquiv.extendScalarsHomOfSurjective (A := Ω) hsurj
  have hval (τ : (actualNormalizationInertiaGroup p.toValuationSubring F Ω Q).carrier) :
      i (genericPlaceInertiaHom Y p Q hsurj τ) =
        fieldSourceAbsoluteGaloisHom F Ω jF τ.val := by
    have h := fieldSourceAbsoluteGaloisHom_naturality F Y.functionField Ω
      f (Y.fromSpecStalk (genericPoint Y)) jF hpoint (e τ.val)
    have he : (e τ.val).restrictScalars F = τ.val := by
      apply AlgEquiv.ext
      intro z
      rfl
    rw [he] at h
    change pointedFundamentalGroupHom f xi (ξ F Ω ≫ jF) hpoint
      (genericPlaceInertiaHom Y p Q hsurj τ) = _
    rw [namedModel_pointedHom_equality_conjugation]
    exact h
  rw [← genericPlaceInertiaHom_range Y p Q hsurj]
  apply Subgroup.ext
  intro z
  constructor
  · rintro ⟨w, ⟨τ, rfl⟩, rfl⟩
    exact ⟨τ.val, τ.property, (hval τ).symm⟩
  · rintro ⟨σ, hσ, rfl⟩
    let τ : (actualNormalizationInertiaGroup p.toValuationSubring F Ω Q).carrier := ⟨σ, hσ⟩
    exact ⟨genericPlaceInertiaHom Y p Q hsurj τ, ⟨τ, rfl⟩, hval τ⟩

end AnabelianGeometry.WeightFiltration

namespace AlgebraicGeometry.Scheme

/-- Cancel the actual model open immersion in the named cover's retained
root-generic equality. No new generic-point compatibility is requested. -/
theorem namedModel_root_chart_comp
    {F A : Type} [Field F] [CommRing A]
    {C X W : Scheme} [IsIntegral C] [IsIntegral X]
    (E : F ≃+* C.functionField) (i : X ⟶ C) [IsOpenImmersion i]
    (J : W ≅ X) (g : Spec (.of A) ⟶ W) (eRoot : A ≃+* F)
    (hgeneric : g ≫ J.hom ≫ i =
      Spec.map (CommRingCat.ofHom eRoot.symm.toRingHom) ≫ C.functionFieldChartPoint E) :
    g ≫ J.hom = Spec.map (CommRingCat.ofHom eRoot.symm.toRingHom) ≫
      X.functionFieldChartPoint (E.trans i.functionFieldRingEquivOfIsOpenImmersion) := by
  apply (cancel_mono i).mp
  rw [Category.assoc, hgeneric, Category.assoc,
    functionFieldChartPoint_comp_openImmersion]

/-- In root coordinates the actual named model isomorphism takes the source
field chart to the standard target field chart exactly, with no conjugator. -/
theorem namedModel_coordinate_chart_comp
    {F A : Type} [Field F] [CommRing A]
    {C X W : Scheme} [IsIntegral C] [IsIntegral X]
    (E : F ≃+* C.functionField) (i : X ⟶ C) [IsOpenImmersion i]
    (J : W ≅ X) (g : Spec (.of A) ⟶ W) (eRoot : A ≃+* F)
    (hgeneric : g ≫ J.hom ≫ i =
      Spec.map (CommRingCat.ofHom eRoot.symm.toRingHom) ≫ C.functionFieldChartPoint E) :
    (Spec.map (CommRingCat.ofHom eRoot.toRingHom) ≫ g) ≫ J.hom =
      X.functionFieldChartPoint (E.trans i.functionFieldRingEquivOfIsOpenImmersion) := by
  have hcancel : eRoot.toRingHom.comp eRoot.symm.toRingHom = RingHom.id F := by
    ext z
    exact eRoot.apply_symm_apply z
  rw [Category.assoc, namedModel_root_chart_comp E i J g eRoot hgeneric,
    ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcancel]
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- The same chart equality after extension to the original ambient field. -/
theorem namedModel_coordinate_ambient_comp
    {F A Ω : Type} [Field F] [CommRing A] [Field Ω] [Algebra F Ω]
    {C X W : Scheme} [IsIntegral C] [IsIntegral X]
    (E : F ≃+* C.functionField) (i : X ⟶ C) [IsOpenImmersion i]
    (J : W ≅ X) (g : Spec (.of A) ⟶ W) (eRoot : A ≃+* F)
    (hgeneric : g ≫ J.hom ≫ i =
      Spec.map (CommRingCat.ofHom eRoot.symm.toRingHom) ≫ C.functionFieldChartPoint E) :
    (ξ F Ω ≫ (Spec.map (CommRingCat.ofHom eRoot.toRingHom) ≫ g)) ≫ J.hom =
      ξ F Ω ≫ X.functionFieldChartPoint
        (E.trans i.functionFieldRingEquivOfIsOpenImmersion) := by
  rw [Category.assoc, namedModel_coordinate_chart_comp E i J g eRoot hgeneric]

end AlgebraicGeometry.Scheme

namespace AnabelianGeometry.WeightFiltration

/-- The actual named-model isomorphism transports every chosen absolute
inertia subgroup through the original root-field chart. Applied to the
localized normalization prime, this supplies its precise model-side image.
The point equality is derived from the existing named-model output. -/
theorem namedModel_absoluteSubgroup_pointed_image
    {F A Ω : Type} [Field F] [CommRing A] [Field Ω] [Algebra F Ω]
    [IsSepClosure F Ω] [IsSepClosed Ω]
    {C X W : Scheme} [IsIntegral C] [IsIntegral X] [IsIntegral W]
    (E : F ≃+* C.functionField) (i : X ⟶ C) [IsOpenImmersion i]
    (J : W ≅ X) (g : Spec (.of A) ⟶ W) (eRoot : A ≃+* F)
    (hgeneric : g ≫ J.hom ≫ i =
      Spec.map (CommRingCat.ofHom eRoot.symm.toRingHom) ≫ C.functionFieldChartPoint E)
    (I : Subgroup Gal(Ω/F)) :
    let jW := Spec.map (CommRingCat.ofHom eRoot.toRingHom) ≫ g
    let jX := X.functionFieldChartPoint (E.trans i.functionFieldRingEquivOfIsOpenImmersion)
    let hpoint := Scheme.namedModel_coordinate_ambient_comp
      (Ω := Ω) E i J g eRoot hgeneric
    (I.map (fieldSourceAbsoluteGaloisHom F Ω jW).toMonoidHom).map
      (pointedFundamentalGroupHom J.hom (ξ F Ω ≫ jW) (ξ F Ω ≫ jX) hpoint).toMonoidHom =
        I.map (fieldSourceAbsoluteGaloisHom F Ω jX).toMonoidHom := by
  intro jW jX hpoint
  have hval (σ : Gal(Ω/F)) :
      pointedFundamentalGroupHom J.hom (ξ F Ω ≫ jW) (ξ F Ω ≫ jX) hpoint
        (fieldSourceAbsoluteGaloisHom F Ω jW σ) =
          fieldSourceAbsoluteGaloisHom F Ω jX σ := by
    have h := fieldSourceAbsoluteGaloisHom_naturality F F Ω J.hom jW jX hpoint σ
    have hs : σ.restrictScalars F = σ := by
      apply AlgEquiv.ext
      intro z
      rfl
    rw [hs] at h
    rw [namedModel_pointedHom_equality_conjugation]
    exact h
  rw [Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro σ
  exact hval σ

end AnabelianGeometry.WeightFiltration

namespace AlgebraicGeometry.FiniteEtale

open EtaleFundamentalGroups

/-- The generic point used by connectedCover_actualPlaceInertia_image is
literally the point selected by w in matchedFiberCoverGroupTransport.
The ambient algebra is the embedding reconstructed from this same w. -/
theorem actualFiberPointLift_eq_genericExtension_of_embedding
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U]
    (Ω : Type) [Field Ω] [IsSepClosed Ω] [Algebra U.functionField Ω]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
    letI : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let g := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
    let emb := finiteEtaleGenericHomFunctionFieldAlgHom W g
    letI : Algebra W.left.functionField Ω := emb.toRingHom.toAlgebra
    W.left.genericExtensionMorphism Ω =
      actualFiberPointLift (U.genericExtensionMorphism Ω) W w := by
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
  let g := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
  let emb := finiteEtaleGenericHomFunctionFieldAlgHom W g
  let : Algebra W.left.functionField Ω := emb.toRingHom.toAlgebra
  change Spec.map (CommRingCat.ofHom emb.toRingHom) ≫
    W.left.fromSpecStalk (genericPoint W.left) = g.left
  exact finiteEtaleGenericHomFunctionFieldAlgHom_spec W g

end AlgebraicGeometry.FiniteEtale
