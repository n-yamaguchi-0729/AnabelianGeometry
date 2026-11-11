/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.CompactificationBoundary
public import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumPurityNormalization
public import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedRestriction
public import Nyll.SchemeTheory.Normalization.SourceIso
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Functorial compactifications of actual connected covers

A morphism of connected finite étale covers induces its literal map on
function fields, hence a map of the relative normalizations of the ambient
scheme. The normalization universal property proves the identity and
composition laws. The original open inclusions are natural for these maps.

Any diagram of connected finite étale covers therefore gives a diagram of
their actual compactifications over the ambient scheme, in every
characteristic.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u v w

variable {X U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]

attribute [local instance] connectedLeftIntegral

private theorem connectedCoverGenericMorphism_eq_fromSpecStalk
    (W : FiniteEtale U) [IsConnected W] :
    connectedCoverGenericMorphism W = W.left.fromSpecStalk (genericPoint W.left) := by
  unfold connectedCoverGenericMorphism Scheme.genericExtensionMorphism
  rw [show CommRingCat.ofHom
      (algebraMap W.left.functionField W.left.functionField) = 𝟙 _ from rfl,
    Spec.map_id, Category.id_comp]

private local instance connectedCoverGenericMorphism_mono
    (W : FiniteEtale U) [IsConnected W] : Mono (connectedCoverGenericMorphism W) := by
  rw [connectedCoverGenericMorphism_eq_fromSpecStalk]
  infer_instance

private local instance connectedCoverGenericMorphism_isDominant
    (W : FiniteEtale U) [IsConnected W] : IsDominant (connectedCoverGenericMorphism W) := by
  rw [connectedCoverGenericMorphism_eq_fromSpecStalk]
  refine ⟨?_⟩
  have hη : genericPoint W.left ∈ Set.range (W.left.fromSpecStalk (genericPoint W.left)) :=
    ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
  have hd : Dense ({genericPoint W.left} : Set W.left) :=
    dense_iff_closure_eq.mpr (genericPoint_spec W.left).def
  exact hd.mono (Set.singleton_subset_iff.mpr hη)

/-- A morphism between connected finite étale covers has dense image. -/
theorem connectedCoverMap_denseRange
    {W V : FiniteEtale U} [IsConnected W] [IsConnected V] (f : W ⟶ V) :
    DenseRange f.left := by
  have : Surjective f.left := IsFiniteEtale.surjective f.left
  exact f.left.surjective.denseRange

/-- The actual morphism of generic field spectra induced by a cover morphism. -/
def connectedCoverGenericMap
    {W V : FiniteEtale U} [IsConnected W] [IsConnected V] (f : W ⟶ V) :
    Spec (.of W.left.functionField) ⟶ Spec (.of V.left.functionField) :=
  Spec.map (CommRingCat.ofHom (f.left.functionFieldMap (connectedCoverMap_denseRange f)))

/-- The generic spectrum map commutes with the actual cover morphism. -/
@[reassoc]
theorem connectedCoverGenericMap_comp_genericMorphism
    {W V : FiniteEtale U} [IsConnected W] [IsConnected V] (f : W ⟶ V) :
    connectedCoverGenericMap f ≫ connectedCoverGenericMorphism V =
      connectedCoverGenericMorphism W ≫ f.left :=
  genericExtensionMorphism_functionFieldMap f.left (connectedCoverMap_denseRange f)

/-- Generic spectrum maps preserve identities. -/
theorem connectedCoverGenericMap_id (W : FiniteEtale U) [IsConnected W] :
    connectedCoverGenericMap (𝟙 W) = 𝟙 (Spec (.of W.left.functionField)) := by
  apply (cancel_mono (connectedCoverGenericMorphism W)).mp
  rw [connectedCoverGenericMap_comp_genericMorphism, Category.id_comp]
  exact Category.comp_id _

/-- Generic spectrum maps preserve composition. -/
theorem connectedCoverGenericMap_comp
    {W V Z : FiniteEtale U} [IsConnected W] [IsConnected V] [IsConnected Z]
    (f : W ⟶ V) (g : V ⟶ Z) :
    connectedCoverGenericMap (f ≫ g) =
      connectedCoverGenericMap f ≫ connectedCoverGenericMap g := by
  apply (cancel_mono (connectedCoverGenericMorphism Z)).mp
  rw [Category.assoc, connectedCoverGenericMap_comp_genericMorphism g,
    ← Category.assoc, connectedCoverGenericMap_comp_genericMorphism f,
    Category.assoc, connectedCoverGenericMap_comp_genericMorphism (f ≫ g)]
  rfl

variable (j : U ⟶ X)

/-- The generic map of covers commutes with the map to the ambient scheme. -/
theorem connectedCoverGenericMap_over
    {W V : FiniteEtale U} [IsConnected W] [IsConnected V] (f : W ⟶ V) :
    connectedCoverGenericMap f ≫ (connectedCoverGenericComposite V ≫ j) =
      connectedCoverGenericComposite W ≫ j := by
  have hf : f.left ≫ V.hom = W.hom := f.w
  unfold connectedCoverGenericComposite
  rw [← Category.assoc, ← Category.assoc, connectedCoverGenericMap_comp_genericMorphism,
    Category.assoc (connectedCoverGenericMorphism W) f.left V.hom, hf]

/-- The actual transition map between the normalization compactifications. -/
def connectedCoverCompactificationMap
    {W V : FiniteEtale U} [IsConnected W] [IsConnected V] (f : W ⟶ V) :
    (connectedCoverGenericComposite W ≫ j).normalization ⟶
      (connectedCoverGenericComposite V ≫ j).normalization :=
  Scheme.Hom.normalizationSourceMap
    (connectedCoverGenericComposite W ≫ j) (connectedCoverGenericComposite V ≫ j)
    (connectedCoverGenericMap f) (connectedCoverGenericMap_over j f)

/-- Compactification maps commute with their structural maps to the ambient scheme. -/
@[reassoc]
theorem connectedCoverCompactificationMap_fromNormalization
    {W V : FiniteEtale U} [IsConnected W] [IsConnected V] (f : W ⟶ V) :
    connectedCoverCompactificationMap j f ≫
        (connectedCoverGenericComposite V ≫ j).fromNormalization =
      (connectedCoverGenericComposite W ≫ j).fromNormalization :=
  Scheme.Hom.normalizationSourceMap_fromNormalization _ _ _ _

/-- Compactification maps retain the actual generic field spectrum map. -/
@[reassoc]
theorem toNormalization_connectedCoverCompactificationMap
    {W V : FiniteEtale U} [IsConnected W] [IsConnected V] (f : W ⟶ V) :
    (connectedCoverGenericComposite W ≫ j).toNormalization ≫
        connectedCoverCompactificationMap j f =
      connectedCoverGenericMap f ≫ (connectedCoverGenericComposite V ≫ j).toNormalization :=
  Scheme.Hom.toNormalization_normalizationSourceMap _ _ _ _

/-- The transition at an identity cover morphism is the identity. -/
theorem connectedCoverCompactificationMap_id (W : FiniteEtale U) [IsConnected W] :
    connectedCoverCompactificationMap j (𝟙 W) =
      𝟙 (connectedCoverGenericComposite W ≫ j).normalization := by
  apply Scheme.Hom.normalization.hom_ext (connectedCoverGenericComposite W ≫ j)
    _ _ (connectedCoverGenericComposite W ≫ j).fromNormalization
  · rw [toNormalization_connectedCoverCompactificationMap, connectedCoverGenericMap_id,
      Category.id_comp, Category.comp_id]
  · exact connectedCoverCompactificationMap_fromNormalization j (𝟙 W)
  · exact Category.id_comp _

/-- The actual compactification transition maps compose. -/
theorem connectedCoverCompactificationMap_comp
    {W V Z : FiniteEtale U} [IsConnected W] [IsConnected V] [IsConnected Z]
    (f : W ⟶ V) (g : V ⟶ Z) :
    connectedCoverCompactificationMap j (f ≫ g) =
      connectedCoverCompactificationMap j f ≫ connectedCoverCompactificationMap j g := by
  apply Scheme.Hom.normalization.hom_ext (connectedCoverGenericComposite W ≫ j)
    _ _ (connectedCoverGenericComposite Z ≫ j).fromNormalization
  · rw [toNormalization_connectedCoverCompactificationMap,
      ← Category.assoc, toNormalization_connectedCoverCompactificationMap,
      Category.assoc, toNormalization_connectedCoverCompactificationMap,
      connectedCoverGenericMap_comp, Category.assoc]
  · exact connectedCoverCompactificationMap_fromNormalization j (f ≫ g)
  · rw [Category.assoc, connectedCoverCompactificationMap_fromNormalization,
      connectedCoverCompactificationMap_fromNormalization]

/-- Every actual connected covering diagram has its actual compactification diagram. -/
def connectedCoverCompactificationDiagram
    {I : Type v} [Category.{w} I] (D : I ⥤ FiniteEtale U)
    [∀ i, IsConnected (D.obj i)] : I ⥤ Over X where
  obj i := Over.mk (connectedCoverGenericComposite (D.obj i) ≫ j).fromNormalization
  map f := Over.homMk (connectedCoverCompactificationMap j (D.map f))
    (connectedCoverCompactificationMap_fromNormalization j (D.map f))
  map_id i := by
    apply Over.OverMorphism.ext
    change connectedCoverCompactificationMap j (D.map (𝟙 i)) = _
    rw [D.map_id, connectedCoverCompactificationMap_id]
    rfl
  map_comp f g := by
    apply Over.OverMorphism.ext
    change connectedCoverCompactificationMap j (D.map (f ≫ g)) = _
    rw [D.map_comp, connectedCoverCompactificationMap_comp]
    rfl

variable [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
  [IsLocallyNoetherian U] [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]

/-- Every actual compactification transition is finite. -/
theorem connectedCoverCompactificationMap_isFinite
    {W V : FiniteEtale U} [IsConnected W] [IsConnected V] (f : W ⟶ V) :
    IsFinite (connectedCoverCompactificationMap j f) := by
  have : IsFinite (connectedCoverCompactificationMap j f ≫
      (connectedCoverGenericComposite V ≫ j).fromNormalization) := by
    rw [connectedCoverCompactificationMap_fromNormalization]
    exact connectedCoverCompactification_isFinite j W
  exact IsFinite.of_comp (connectedCoverCompactificationMap j f)
    (connectedCoverGenericComposite V ≫ j).fromNormalization

/-- Every actual compactification transition is surjective, including on the boundary. -/
theorem connectedCoverCompactificationMap_surjective
    {W V : FiniteEtale U} [IsConnected W] [IsConnected V] (f : W ⟶ V) :
    Function.Surjective (connectedCoverCompactificationMap j f) := by
  have : IsFinite (connectedCoverCompactificationMap j f) :=
    connectedCoverCompactificationMap_isFinite j f
  have : Surjective (connectedCoverGenericMap f) := inferInstance
  have : IsDominant ((connectedCoverGenericComposite W ≫ j).toNormalization ≫
      connectedCoverCompactificationMap j f) := by
    rw [toNormalization_connectedCoverCompactificationMap]
    infer_instance
  have : IsDominant (connectedCoverCompactificationMap j f) :=
    IsDominant.of_comp (connectedCoverGenericComposite W ≫ j).toNormalization
      (connectedCoverCompactificationMap j f)
  have : Surjective (connectedCoverCompactificationMap j f) :=
    surjective_of_isDominant_of_isClosed_range _
      (connectedCoverCompactificationMap j f).isClosedMap.isClosed_range
  exact (connectedCoverCompactificationMap j f).surjective

omit [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] in
/-- The compactification transition extends the original finite étale cover map. -/
@[reassoc]
theorem connectedCoverCompactificationInclusion_naturality
    {W V : FiniteEtale U} [IsConnected W] [IsConnected V] (f : W ⟶ V) :
    connectedCoverCompactificationInclusion j W ≫ connectedCoverCompactificationMap j f =
      f.left ≫ connectedCoverCompactificationInclusion j V := by
  have hf : f.left ≫ V.hom = W.hom := f.w
  refine ext_of_isDominant_of_isSeparated
    (connectedCoverGenericComposite V ≫ j).fromNormalization ?_
    (connectedCoverGenericMorphism W) ?_
  · rw [Category.assoc, connectedCoverCompactificationMap_fromNormalization,
      connectedCoverCompactificationInclusion_comp, Category.assoc,
      connectedCoverCompactificationInclusion_comp, ← Category.assoc, hf]
  · have hW : connectedCoverGenericMorphism W ≫ connectedCoverCompactificationInclusion j W =
        (connectedCoverGenericComposite W ≫ j).toNormalization :=
      connectedCoverGenericMorphism_normalizationPullbackIso_fst W j
    have hV : connectedCoverGenericMorphism V ≫ connectedCoverCompactificationInclusion j V =
        (connectedCoverGenericComposite V ≫ j).toNormalization :=
      connectedCoverGenericMorphism_normalizationPullbackIso_fst V j
    calc
      connectedCoverGenericMorphism W ≫
          (connectedCoverCompactificationInclusion j W ≫ connectedCoverCompactificationMap j f) =
          (connectedCoverGenericComposite W ≫ j).toNormalization ≫
            connectedCoverCompactificationMap j f := by
        rw [← Category.assoc, hW]
      _ = connectedCoverGenericMap f ≫
          (connectedCoverGenericComposite V ≫ j).toNormalization :=
        toNormalization_connectedCoverCompactificationMap j f
      _ = connectedCoverGenericMorphism W ≫
          (f.left ≫ connectedCoverCompactificationInclusion j V) := by
        rw [← hV, ← Category.assoc, connectedCoverGenericMap_comp_genericMorphism,
          Category.assoc]

omit [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] in
/-- A transition preserves and reflects membership in the actual boundary. -/
theorem connectedCoverCompactificationMap_mem_boundary_iff
    {W V : FiniteEtale U} [IsConnected W] [IsConnected V] (f : W ⟶ V)
    (y : (connectedCoverGenericComposite W ≫ j).normalization) :
    connectedCoverCompactificationMap j f y ∉
        Set.range (connectedCoverCompactificationInclusion j V) ↔
      y ∉ Set.range (connectedCoverCompactificationInclusion j W) := by
  rw [not_mem_range_connectedCoverCompactificationInclusion,
    not_mem_range_connectedCoverCompactificationInclusion]
  have h := congrArg (fun q => q y) (connectedCoverCompactificationMap_fromNormalization j f)
  change (connectedCoverGenericComposite V ≫ j).fromNormalization
      (connectedCoverCompactificationMap j f y) =
    (connectedCoverGenericComposite W ≫ j).fromNormalization y at h
  rw [h]

end AlgebraicGeometry.FiniteEtale
