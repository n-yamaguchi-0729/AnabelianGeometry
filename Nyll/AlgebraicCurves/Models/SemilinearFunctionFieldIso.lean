/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.FunctionFields.CurveModelIsoFunctionField
public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.IsoCompEqOpenImmersion
public import Nyll.AlgebraicCurves.Places.Basic
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Nyll.SchemeTheory.FunctionFields.StalkFunctoriality
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality
public import Nyll.SchemeTheory.FunctionFields.OpenImmersion
public import Nyll.GaloisCohomology.Topology.FiniteFieldAbelian

/-!
# Realizing a semilinear function-field isomorphism on the original models

The constant-field isomorphism is retained. In particular, no linearity over
the chosen constants is inferred from an isomorphism of arithmetic groups.
The resulting scheme isomorphism realizes the specified inverse field map,
and its original closed points are the prescribed places when orders agree.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- An isomorphism between nonempty open curves extends to their actual
smooth proper compactifications with the same coefficient automorphism.
This applies to arithmetic deck transformations acting on the full constants. -/
theorem exists_semilinear_compactificationIso
    {K : Type u} [Field K] {X Y U V : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [Nonempty U]
    (cX : X ⟶ Spec (.of K)) (cY : Y ⟶ Spec (.of K))
    [IsProper cX] [SmoothOfRelativeDimension 1 cX]
    [IsProper cY] [SmoothOfRelativeDimension 1 cY]
    (jX : U ⟶ X) (jY : V ⟶ Y) [IsOpenImmersion jX] [IsOpenImmersion jY]
    (s : U ≅ V) (τ : K ≃+* K)
    (hs : s.hom ≫ (jY ≫ cY) ≫ Spec.map (CommRingCat.ofHom τ.toRingHom) = jX ≫ cX) :
    ∃ t : X ≅ Y, jX ≫ t.hom = s.hom ≫ jY ∧
      t.hom ≫ cY ≫ Spec.map (CommRingCat.ofHom τ.toRingHom) = cX := by
  let b : Spec (.of K) ≅ Spec (.of K) := Scheme.Spec.mapIso τ.toCommRingCatIso.op
  let cYτ : Y ⟶ Spec (.of K) := cY ≫ b.hom
  have : Smooth cY := SmoothOfRelativeDimension.smooth (n := 1) (f := cY)
  have : IsProper cYτ := inferInstance
  have : Smooth cYτ := inferInstance
  let W : X.Opens := jX.opensRange
  let d : (W : Scheme) ⟶ Y := jX.isoOpensRange.inv ≫ s.hom ≫ jY
  have hW : (W : Set X).Nonempty := by
    obtain ⟨u⟩ := (inferInstance : Nonempty U)
    exact ⟨jX u, ⟨u, rfl⟩⟩
  have hd : d ≫ cYτ = W.ι ≫ cX := by
    change (jX.isoOpensRange.inv ≫ s.hom ≫ jY) ≫
      (cY ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)) = W.ι ≫ cX
    calc
      _ = jX.isoOpensRange.inv ≫
          (s.hom ≫ (jY ≫ cY) ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)) := by
        simp only [Category.assoc]
      _ = jX.isoOpensRange.inv ≫ (jX ≫ cX) := by rw [hs]
      _ = W.ι ≫ cX := Scheme.Hom.isoOpensRange_inv_comp_assoc jX cX
  obtain ⟨t, ht, hWmap⟩ :=
    exists_iso_comp_eq_of_isOpenImmersion_of_isProper cX cYτ W hW d hd
  refine ⟨t, ?_, ht⟩
  calc
    jX ≫ t.hom = jX.isoOpensRange.hom ≫ (W.ι ≫ t.hom) := by
      rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    _ = jX.isoOpensRange.hom ≫ d := by rw [hWmap]
    _ = s.hom ≫ jY := by
      change jX.isoOpensRange.hom ≫ (jX.isoOpensRange.inv ≫ s.hom ≫ jY) = _
      rw [Iso.hom_inv_id_assoc]

/-- Any isomorphism of nonempty open curves over a finite field extends
to their given smooth proper compactifications. Its scalar automorphism is
constructed from the actual function-field isomorphism. -/
theorem exists_compactificationIso_of_finite_base
    {K : Type u} [Field K] [Finite K] {X Y U V : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral U] [IsIntegral V]
    (cX : X ⟶ Spec (.of K)) (cY : Y ⟶ Spec (.of K))
    [IsProper cX] [SmoothOfRelativeDimension 1 cX]
    [IsProper cY] [SmoothOfRelativeDimension 1 cY]
    (jX : U ⟶ X) (jY : V ⟶ Y) [IsOpenImmersion jX] [IsOpenImmersion jY]
    (s : U ≅ V) :
    ∃ t : X ≅ Y, jX ≫ t.hom = s.hom ≫ jY := by
  let : Algebra K U.functionField := (AlgebraicCurve.baseToFunctionField (jX ≫ cX)).toAlgebra
  let : Algebra K V.functionField := (AlgebraicCurve.baseToFunctionField (jY ≫ cY)).toAlgebra
  let Φ : U.functionField ≃+* V.functionField :=
    s.hom.functionFieldRingEquivOfIsOpenImmersion.symm
  obtain ⟨τ, hτ⟩ := GaloisCohomology.exists_finiteBaseAutomorphism_of_ringEquiv K Φ
  let pU := U.fromSpecStalk (genericPoint U)
  let pV := V.fromSpecStalk (genericPoint V)
  have : IsDominant pU := FiniteEtale.genericPoint_isDominant U
  have hpU : pU ≫ (jX ≫ cX) =
      Spec.map (CommRingCat.ofHom (algebraMap K U.functionField)) :=
    AlgebraicCurve.fromSpecStalk_genericPoint_comp_base (jX ≫ cX)
  have hpV : pV ≫ (jY ≫ cY) =
      Spec.map (CommRingCat.ofHom (algebraMap K V.functionField)) :=
    AlgebraicCurve.fromSpecStalk_genericPoint_comp_base (jY ≫ cY)
  have hsource : pU ≫ s.hom = Spec.map (CommRingCat.ofHom Φ.symm.toRingHom) ≫ pV :=
    (EtaleFundamentalGroups.Spec_functionFieldMap_fromSpecStalk s.hom
      (Scheme.Hom.denseRange_of_isOpenImmersion s.hom)).symm
  have hcoeff : CommRingCat.ofHom τ.toRingHom ≫
      CommRingCat.ofHom (algebraMap K V.functionField) ≫
        CommRingCat.ofHom Φ.symm.toRingHom =
      CommRingCat.ofHom (algebraMap K U.functionField) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change Φ.symm (algebraMap K V.functionField (τ z)) = algebraMap K U.functionField z
    rw [← hτ, Φ.symm_apply_apply]
  have hs : s.hom ≫ (jY ≫ cY) ≫ Spec.map (CommRingCat.ofHom τ.toRingHom) = jX ≫ cX := by
    apply ext_of_isDominant pU
    calc
      pU ≫ (s.hom ≫ (jY ≫ cY) ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)) =
          Spec.map (CommRingCat.ofHom Φ.symm.toRingHom) ≫
            (pV ≫ (jY ≫ cY)) ≫ Spec.map (CommRingCat.ofHom τ.toRingHom) := by
        rw [← Category.assoc pU s.hom, hsource]
        simp only [Category.assoc]
      _ = Spec.map (CommRingCat.ofHom Φ.symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K V.functionField)) ≫
            Spec.map (CommRingCat.ofHom τ.toRingHom) := by rw [hpV]
      _ = Spec.map (CommRingCat.ofHom (algebraMap K U.functionField)) := by
        rw [← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hcoeff]
      _ = pU ≫ (jX ≫ cX) := hpU.symm
  obtain ⟨t, ht, _⟩ := exists_semilinear_compactificationIso cX cY jX jY s τ hs
  exact ⟨t, ht⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicCurve.CurveModel

universe u v w

variable {K₁ K₂ : Type u} [Field K₁] [Field K₂]
  {F₁ : Type v} {F₂ : Type w} [Field F₁] [Field F₂]
  [Algebra K₁ F₁] [Algebra K₂ F₂]

/-- The same field isomorphism extends to the original proper smooth models;
the scalar isomorphism remains in the actual structural-map equation. -/
theorem exists_semilinear_iso_functionFieldMap_eq
    (σ : K₁ ≃+* K₂) (φ : F₁ ≃+* F₂)
    (hφ : ∀ a, φ (algebraMap K₁ F₁ a) = algebraMap K₂ F₂ (σ a))
    (M₁ : CurveModel K₁ F₁) (M₂ : CurveModel K₂ F₂) :
    ∃ e : M₁.C ≅ M₂.C,
      e.hom ≫ M₂.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) = M₁.toBase ∧
      ∀ (hdense : DenseRange e.hom) (z : F₂),
        e.hom.functionFieldMap hdense (M₂.ffEquiv z) = M₁.ffEquiv (φ.symm z) := by
  let a : Spec (.of K₂) ≅ Spec (.of K₁) :=
    Scheme.Spec.mapIso σ.toCommRingCatIso.op
  let c₂ : M₂.C ⟶ Spec (.of K₁) := M₂.toBase ≫ a.hom
  have : Smooth M₂.toBase :=
    SmoothOfRelativeDimension.smooth (n := 1) (f := M₂.toBase)
  have : IsProper c₂ := inferInstance
  have : Smooth c₂ := inferInstance
  let ψr : M₁.C.functionField ≃+* M₂.C.functionField :=
    M₁.ffEquiv.symm.trans (φ.trans M₂.ffEquiv)
  let ψ : M₁.C.functionField ≅ M₂.C.functionField := ψr.toCommRingCatIso
  have hψinv (z : M₂.C.functionField) :
      ψ.inv.hom z = M₁.ffEquiv (φ.symm (M₂.ffEquiv.symm z)) := rfl
  have hb : CommRingCat.ofHom σ.toRingHom ≫
      CommRingCat.ofHom (baseToFunctionField M₂.toBase) ≫ ψ.inv =
      CommRingCat.ofHom (baseToFunctionField M₁.toBase) := by
    ext b
    change ψ.inv.hom (baseToFunctionField M₂.toBase (σ b)) =
      baseToFunctionField M₁.toBase b
    rw [hψinv, ← M₂.ffEquiv_algebraMap, RingEquiv.symm_apply_apply,
      ← hφ b, RingEquiv.symm_apply_apply, M₁.ffEquiv_algebraMap]
  have hψ : Spec.map ψ.inv ≫ M₂.C.fromSpecStalk (genericPoint M₂.C) ≫ c₂ =
      M₁.C.fromSpecStalk (genericPoint M₁.C) ≫ M₁.toBase := by
    change Spec.map ψ.inv ≫ M₂.C.fromSpecStalk (genericPoint M₂.C) ≫
      M₂.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) = _
    rw [← Category.assoc (M₂.C.fromSpecStalk (genericPoint M₂.C)) M₂.toBase,
      AlgebraicCurve.fromSpecStalk_genericPoint_comp_base,
      AlgebraicCurve.fromSpecStalk_genericPoint_comp_base,
      ← Spec.map_comp, ← Spec.map_comp, Category.assoc, hb]
  obtain ⟨e, he, -, hfield⟩ :=
    AlgebraicGeometry.Scheme.exists_iso_functionFieldMap_eq M₁.toBase c₂ ψ hψ
  refine ⟨e, he, fun hdense z => ?_⟩
  have hz := congrArg (fun q : M₂.C.functionField ⟶ M₁.C.functionField =>
    q.hom (M₂.ffEquiv z)) (hfield hdense)
  exact hz.trans (by rw [hψinv, RingEquiv.symm_apply_apply])

/-- Realizing the specified field map also realizes its literal spectrum
map on the original model generic sources. -/
theorem genericSource_comp_iso_eq_of_functionFieldMap
    {F₁ F₂ : Type u} [Field F₁] [Field F₂] [Algebra K₁ F₁] [Algebra K₂ F₂]
    (φ : F₁ ≃+* F₂) (M₁ : CurveModel K₁ F₁) (M₂ : CurveModel K₂ F₂)
    (e : M₁.C ≅ M₂.C)
    (hfield : ∀ (hdense : DenseRange e.hom) (z : F₂),
      e.hom.functionFieldMap hdense (M₂.ffEquiv z) = M₁.ffEquiv (φ.symm z)) :
    (Spec.map (CommRingCat.ofHom M₁.ffEquiv.symm.toRingHom) ≫
        M₁.C.fromSpecStalk (genericPoint M₁.C)) ≫ e.hom =
      Spec.map (CommRingCat.ofHom φ.symm.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom M₂.ffEquiv.symm.toRingHom) ≫
          M₂.C.fromSpecStalk (genericPoint M₂.C)) := by
  have hdense : DenseRange e.hom :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).surjective.denseRange
  have hcoeff : CommRingCat.ofHom (e.hom.functionFieldMap hdense) ≫
      CommRingCat.ofHom M₁.ffEquiv.symm.toRingHom =
      CommRingCat.ofHom M₂.ffEquiv.symm.toRingHom ≫
        CommRingCat.ofHom φ.symm.toRingHom := by
    ext z
    change M₁.ffEquiv.symm (e.hom.functionFieldMap hdense z) =
      φ.symm (M₂.ffEquiv.symm z)
    apply M₁.ffEquiv.injective
    rw [RingEquiv.apply_symm_apply]
    have h := hfield hdense (M₂.ffEquiv.symm z)
    rw [RingEquiv.apply_symm_apply] at h
    exact h
  rw [Category.assoc,
    ← EtaleFundamentalGroups.Spec_functionFieldMap_fromSpecStalk e.hom hdense,
    ← Category.assoc, ← Spec.map_comp, hcoeff, Spec.map_comp, Category.assoc]

/-- Membership in the literal stalk image can be tested in the model's
specified valuation subring, with no change of function-field coordinates. -/
theorem ffEquiv_mem_stalk_range_iff
    (M : CurveModel K₁ F₁) (x : closedPoints M.C) (z : F₁) :
    M.ffEquiv z ∈ (algebraMap (M.C.presheaf.stalk x.val) M.C.functionField).range ↔
      z ∈ (M.placeOfPoint x).toValuationSubring := by
  change M.ffEquiv z ∈
    (algebraMap (M.C.presheaf.stalk x.val) M.C.functionField).range ↔
      z ∈ (M.placeOfPoint x).toValuationSubring.toSubring
  rw [← M.range_stalk_eq x]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    change M.ffEquiv.symm (algebraMap _ M.C.functionField b) = z
    rw [hb, RingEquiv.symm_apply_apply]
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    change M.ffEquiv.symm (algebraMap _ M.C.functionField b) = z at hb
    apply M.ffEquiv.symm.injective
    rw [RingEquiv.symm_apply_apply]
    exact hb

/-- The exact function-field map and normalized orders determine the actual
point map of the scheme isomorphism. -/
theorem iso_apply_closedPoint_of_functionFieldMap
    (φ : F₁ ≃+* F₂) (v : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P z, (v P).ord (φ z) = P.ord z)
    (M₁ : CurveModel K₁ F₁) (M₂ : CurveModel K₂ F₂)
    (e : M₁.C ≅ M₂.C)
    (hfield : ∀ (hdense : DenseRange e.hom) (z : F₂),
      e.hom.functionFieldMap hdense (M₂.ffEquiv z) = M₁.ffEquiv (φ.symm z))
    (x : closedPoints M₁.C) :
    e.hom x.val = (M₂.placeEquiv.symm (v (M₁.placeOfPoint x))).val := by
  let H := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)
  have hdense : DenseRange e.hom := H.surjective.denseRange
  have hyclosed : IsClosed ({e.hom x.val} : Set M₂.C) := by
    rw [← Set.image_singleton]
    exact H.isClosedMap _ x.property
  let y : closedPoints M₂.C := ⟨e.hom x.val, hyclosed⟩
  have hmem (z : F₂) :
      z ∈ (M₂.placeOfPoint y).toValuationSubring ↔
        φ.symm z ∈ (M₁.placeOfPoint x).toValuationSubring := by
    rw [← ffEquiv_mem_stalk_range_iff M₂ y z,
      ← ffEquiv_mem_stalk_range_iff M₁ x (φ.symm z), ← hfield hdense z]
    exact (e.hom.functionFieldMap_mem_stalk_range_iff_of_isOpenImmersion
      hdense x.val (M₂.ffEquiv z)).symm
  have hplace : M₂.placeOfPoint y = v (M₁.placeOfPoint x) := by
    apply Place.ext
    ext z
    rw [hmem z]
    by_cases hz : z = 0
    · subst z
      rw [map_zero]
      exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
    · have hz' : φ.symm z ≠ 0 := (map_ne_zero φ.symm).mpr hz
      rw [(M₁.placeOfPoint x).mem_iff_ord_nonneg hz',
        (v (M₁.placeOfPoint x)).mem_iff_ord_nonneg hz,
        ← hord (M₁.placeOfPoint x) (φ.symm z), RingEquiv.apply_symm_apply]
  have hp := congrArg M₂.placeEquiv.symm hplace
  rw [← M₂.placeEquiv_apply, M₂.placeEquiv.symm_apply_apply] at hp
  exact congrArg Subtype.val hp

end AlgebraicCurve.CurveModel
