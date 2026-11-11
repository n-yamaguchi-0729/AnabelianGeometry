/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.FullConstantOpenCoverDomination
public import Nyll.EtaleFundamentalGroups.Normalization.FiniteNormalFieldSourceGeneric
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Retaining a grown proper cover in the canonical compactification

A finite normal model containing the original open cover is its actual
normalization compactification. This identification preserves the generic
source, open immersion, full constants and geometric boundary. In particular,
a proper cover used to enlarge the boundary can seed arbitrary further open
coverings without requiring their proper extensions to be étale.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.FiniteField

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- A finite normal model containing the original connected cover is its
canonical normalization, with both its generic source and open map retained. -/
theorem exists_compactificationIso_of_finite_normal_model
    {C X Y : Scheme}
    [IsLocallyNoetherian C]
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsNormalIntegral Y]
    (j : X ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (A : FiniteEtale X) [IsConnected A]
    (d : Y ⟶ C) [IsFinite d] (a : A.left ⟶ Y) [IsOpenImmersion a]
    (ha : a ≫ d = A.hom ≫ j) :
    ∃ I : (connectedCoverGenericComposite A ≫ j).normalization ≅ Y,
      I.hom ≫ d = (connectedCoverGenericComposite A ≫ j).fromNormalization ∧
      (connectedCoverGenericComposite A ≫ j).toNormalization ≫ I.hom =
        connectedCoverGenericMorphism A ≫ a ∧
      connectedCoverCompactificationInclusion j A ≫ I.hom = a := by
  have : IsIntegral A.left := isIntegral_left_of_isConnected_finiteEtale A
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian d
  let η := connectedCoverGenericMorphism A
  have hη : η = A.left.fromSpecStalk (genericPoint A.left) := by
    unfold η connectedCoverGenericMorphism Scheme.genericExtensionMorphism
    rw [show CommRingCat.ofHom
        (algebraMap A.left.functionField A.left.functionField) = 𝟙 _ from rfl,
      Spec.map_id, Category.id_comp]
  have : IsDominant η := by
    rw [hη]
    refine ⟨?_⟩
    have hmem : genericPoint A.left ∈
        Set.range (A.left.fromSpecStalk (genericPoint A.left)) :=
      ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
    have hdense : Dense ({genericPoint A.left} : Set A.left) :=
      dense_iff_closure_eq.mpr (genericPoint_spec A.left).def
    exact hdense.mono (Set.singleton_subset_iff.mpr hmem)
  have : IsPreimmersion η := by rw [hη]; infer_instance
  have : QuasiCompact η := by rw [hη]; infer_instance
  have : QuasiSeparated η := by rw [hη]; infer_instance
  have : IsDominant a :=
    ⟨a.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace a⟩
  let p := η ≫ a
  have : IsDominant p := by dsimp only [p]; infer_instance
  have : IsPreimmersion p := by dsimp only [p]; infer_instance
  have : QuasiCompact p := by dsimp only [p]; infer_instance
  have : QuasiSeparated p := by dsimp only [p]; infer_instance
  have hp : p ≫ d = connectedCoverGenericComposite A ≫ j := by
    change (η ≫ a) ≫ d = (η ≫ A.hom) ≫ j
    rw [Category.assoc, ha, Category.assoc]
  have transport (q : Spec (.of A.left.functionField) ⟶ C)
      [QuasiCompact q] [QuasiSeparated q] (h : p ≫ d = q) :
      ∃ I : q.normalization ≅ Y,
        I.hom ≫ d = q.fromNormalization ∧ q.toNormalization ≫ I.hom = p := by
    subst q
    exact ⟨finiteNormalFieldSourceIso d p,
      finiteNormalFieldSourceIso_hom_fromNormalization d p,
      toNormalization_finiteNormalFieldSourceIso_hom d p⟩
  obtain ⟨I, hI, hgen⟩ := transport _ hp
  refine ⟨I, hI, hgen, ?_⟩
  refine ext_of_isDominant_of_isSeparated d ?_ η ?_
  · rw [Category.assoc, hI, connectedCoverCompactificationInclusion_comp]
    exact ha.symm
  · have hsource : η ≫ connectedCoverCompactificationInclusion j A =
        (connectedCoverGenericComposite A ≫ j).toNormalization :=
      connectedCoverGenericMorphism_normalizationPullbackIso_fst A j
    exact (congrArg (fun f => f ≫ I.hom) hsource).trans hgen

/-- An actual isomorphism of compactifications identifies their geometric
boundary points and preserves their specified embeddings into the closure. -/
def geometricBoundaryPointEquivOfCompactificationIso
    (L κ : Type) [Field L] [Field κ] [Algebra L κ]
    {C₁ C₂ U : Scheme} (I : C₁ ≅ C₂) (c : C₂ ⟶ Spec (.of L))
    (j₁ : U ⟶ C₁) (j₂ : U ⟶ C₂) (hj : j₁ ≫ I.hom = j₂) :
    GeometricBoundaryPoint L κ (I.hom ≫ c) j₁ ≃
      GeometricBoundaryPoint L κ c j₂ := by
  have hboundary (z : C₁) : I.hom z ∉ Set.range j₂ ↔ z ∉ Set.range j₁ := by
    apply not_congr
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨u, I.hom.homeomorph.injective
        ((congrArg (fun f : U ⟶ C₂ => f u) hj).trans hu)⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u, (congrArg (fun f : U ⟶ C₂ => f u) hj).symm⟩
  refine
    { toFun := fun p => ⟨⟨p.val.val ≫ I.hom, by
        rw [Category.assoc]
        exact p.val.property⟩, (hboundary _).mpr p.property⟩
      invFun := fun p => ⟨⟨p.val.val ≫ I.inv, by
        rw [Category.assoc, I.inv_hom_id_assoc]
        exact p.val.property⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply (hboundary _).mp
    have heq : (p.val.val ≫ I.inv) ≫ I.hom = p.val.val := by
      rw [Category.assoc, I.inv_hom_id, Category.comp_id]
    exact (congrArg (fun f : Spec (.of κ) ⟶ C₂ =>
      f (IsLocalRing.closedPoint κ)) heq).symm ▸ p.property
  · intro p
    apply Subtype.ext
    apply Subtype.ext
    change (p.val.val ≫ I.hom) ≫ I.inv = p.val.val
    rw [Category.assoc, I.hom_inv_id, Category.comp_id]
  · intro p
    apply Subtype.ext
    apply Subtype.ext
    change (p.val.val ≫ I.inv) ≫ I.hom = p.val.val
    rw [Category.assoc, I.inv_hom_id, Category.comp_id]

/-- Transport a grown proper model's full constants to the canonical
normalization without changing its open cover or its geometric boundary. -/
theorem exists_fullConstant_compactification_transport
    {k F : Type} [Field k] [Field F] [Algebra k F]
    (L κ : Type) [Field L] [Field κ] [Algebra k L] [Algebra L κ]
    (M : CurveModel k F) {X Y : Scheme}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsNormalIntegral Y]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (A : FiniteEtale X) [IsConnected A]
    (d : Y ⟶ M.C) [IsFinite d] (a : A.left ⟶ Y) [IsOpenImmersion a]
    (ha : a ≫ d = A.hom ≫ j)
    (c : Y ⟶ Spec (.of L)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    [GeometricallyIntegral c]
    (hc : c ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) = d ≫ M.toBase) :
    ∃ I : (connectedCoverGenericComposite A ≫ j).normalization ≅ Y,
      I.hom ≫ d = (connectedCoverGenericComposite A ≫ j).fromNormalization ∧
      (connectedCoverGenericComposite A ≫ j).toNormalization ≫ I.hom =
        connectedCoverGenericMorphism A ≫ a ∧
      connectedCoverCompactificationInclusion j A ≫ I.hom = a ∧
      (I.hom ≫ c) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
        (connectedCoverGenericComposite A ≫ j).fromNormalization ≫ M.toBase ∧
      IsProper (I.hom ≫ c) ∧ SmoothOfRelativeDimension 1 (I.hom ≫ c) ∧
      GeometricallyIntegral (I.hom ≫ c) ∧
      Nat.card (GeometricBoundaryPoint L κ (I.hom ≫ c)
        (connectedCoverCompactificationInclusion j A)) =
        Nat.card (GeometricBoundaryPoint L κ c a) := by
  have : IsLocallyNoetherian M.C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  obtain ⟨I, hI, hgen, hopen⟩ := exists_compactificationIso_of_finite_normal_model j A d a ha
  have hbase : (I.hom ≫ c) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
      (connectedCoverGenericComposite A ≫ j).fromNormalization ≫ M.toBase := by
    rw [Category.assoc, hc, ← Category.assoc, hI]
  have hsmooth : SmoothOfRelativeDimension 1 (I.hom ≫ c) :=
    smoothOfRelativeDimension_comp 0 1 I.hom c
  let : MorphismProperty.RespectsIso (@GeometricallyIntegral : MorphismProperty Scheme) := by
    rw [GeometricallyIntegral.eq_geometrically, geometrically_eq_universally]
    exact MorphismProperty.universally_respectsIso _
  have hgeom : GeometricallyIntegral (I.hom ≫ c) :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyIntegral) I.hom c).mpr inferInstance
  exact ⟨I, hI, hgen, hopen, hbase, inferInstance, hsmooth, hgeom,
    Nat.card_congr (geometricBoundaryPointEquivOfCompactificationIso L κ I c
      (connectedCoverCompactificationInclusion j A) a hopen)⟩

end AnabelianGeometry.FiniteField
