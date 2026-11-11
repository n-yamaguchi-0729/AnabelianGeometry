/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.ConstantBaseChangeCompactification
public import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
public import Nyll.EtaleFundamentalGroups.GeometricFiber.RecoveredCoverGeometricIntegrality
public import Nyll.SchemeTheory.LocalGeometry.IntegralSmooth

/-!
# Literal curve models after finite constant extension

Connectedness of the original geometric open, together with smoothness,
proves geometric integrality of the open and its original proper model.
The actual constant pullback is then integral and supplies its own literal
curve model over the constant extension. All structural maps are retained.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale TopologicalSpace

namespace AnabelianGeometry.FiniteField

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

private theorem connected_of_geometricallyIntegral
    {X S : Scheme.{uGeom}} (f : X ⟶ S) [GeometricallyIntegral f] : GeometricallyConnected f := by
  constructor
  intro K _ y Z fst snd h
  have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
  infer_instance

variable {k : Type uGeom} {F : Type uField₁} [Field k] [Field F] [Algebra k F]
  (M : CurveModel k F) {U : Scheme.{uGeom}} [IsIntegral U]
  (j : U ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j]
  (κ : Type uGeom) [Field κ] [IsAlgClosed κ] [Algebra k κ]
  [ConnectedSpace ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
    (j ≫ M.toBase))]

omit [IsIntegral U] [QuasiCompact j] in
include κ in
/-- The original connected geometric open is integral by smoothness, so its
actual structure morphism is geometrically integral. -/
theorem curveModel_open_geometricallyIntegral_of_connected_baseChange :
    GeometricallyIntegral (j ≫ M.toBase) := by
  have : SmoothOfRelativeDimension 1 (j ≫ M.toBase) :=
    smoothOfRelativeDimension_comp 0 1 j M.toBase
  have : Smooth (j ≫ M.toBase) := SmoothOfRelativeDimension.smooth 1 (j ≫ M.toBase)
  let b := Spec.map (CommRingCat.ofHom (algebraMap k κ))
  have : IsIntegral (pullback b (j ≫ M.toBase) : Scheme.{uGeom}) :=
    isIntegral_of_smooth_of_preconnectedSpace (pullback.fst b (j ≫ M.toBase))
  exact geometricallyIntegral_of_integral_recovered_cover (j ≫ M.toBase)
    (Iso.refl (pullback b (j ≫ M.toBase)))

include j κ in
/-- The same geometric integrality extends across the original dense open. -/
theorem curveModel_geometricallyIntegral_of_open_connected_baseChange :
    GeometricallyIntegral M.toBase := by
  have : GeometricallyIntegral (j ≫ M.toBase) :=
    curveModel_open_geometricallyIntegral_of_connected_baseChange M j κ
  have : IsDominant j :=
    ⟨j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j⟩
  exact GeometricallyIntegral.of_comp_of_isDominant j M.toBase (Field.toIsField k)
    (inferInstance : GeometricallyIntegral (j ≫ M.toBase))

omit [IsIntegral U] [QuasiCompact j] in
include κ in
/-- Geometric connectedness of the original open follows from the same
specified connected geometric fiber. -/
theorem curveModel_open_geometricallyConnected_of_connected_baseChange :
    GeometricallyConnected (j ≫ M.toBase) := by
  have : GeometricallyIntegral (j ≫ M.toBase) :=
    curveModel_open_geometricallyIntegral_of_connected_baseChange M j κ
  exact connected_of_geometricallyIntegral (j ≫ M.toBase)

include j κ in
/-- Geometric connectedness of the original model is derived, not assumed. -/
theorem curveModel_geometricallyConnected_of_open_connected_baseChange :
    GeometricallyConnected M.toBase := by
  have : GeometricallyIntegral M.toBase :=
    curveModel_geometricallyIntegral_of_open_connected_baseChange M j κ
  exact connected_of_geometricallyIntegral M.toBase

variable (E : IntermediateField k κ)
  [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]

omit [IsIntegral U] [QuasiCompact j] in
/-- The structural map of the actual constant cover is geometrically integral. -/
theorem constantCoverOpen_geometricallyIntegral :
    GeometricallyIntegral
      (pullback.fst (originalConstantFieldCover k E).hom (j ≫ M.toBase)) := by
  have : GeometricallyIntegral (j ≫ M.toBase) :=
    curveModel_open_geometricallyIntegral_of_connected_baseChange M j κ
  infer_instance

omit [IsIntegral U] [QuasiCompact j] in
/-- The actual constant cover is geometrically connected over its own constants. -/
theorem constantCoverOpen_geometricallyConnected :
    GeometricallyConnected
      (pullback.fst (originalConstantFieldCover k E).hom (j ≫ M.toBase)) := by
  have : GeometricallyIntegral
      (pullback.fst (originalConstantFieldCover k E).hom (j ≫ M.toBase)) :=
    constantCoverOpen_geometricallyIntegral M j κ E
  exact connected_of_geometricallyIntegral
    (pullback.fst (originalConstantFieldCover k E).hom (j ≫ M.toBase))

omit [IsIntegral U] [QuasiCompact j] in
/-- The literal geometric base change of the actual constant cover is connected. -/
theorem constantCoverOpen_geometric_connected :
    ConnectedSpace ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (pullback.fst (originalConstantFieldCover k E).hom (j ≫ M.toBase))) := by
  have hgc : GeometricallyConnected
      (pullback.fst (originalConstantFieldCover k E).hom (j ≫ M.toBase)) :=
    constantCoverOpen_geometricallyConnected M j κ E
  exact hgc.geometrically_connectedSpace
    (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
    (pullback.snd _ _) (pullback.fst _ _) (IsPullback.of_hasPullback _ _).flip

include j in
/-- The literal base-changed compactification is integral. -/
theorem constantCoverModel_isIntegral :
    IsIntegral (constantBaseChangeCompactification k E M.toBase) := by
  have : GeometricallyIntegral M.toBase :=
    curveModel_geometricallyIntegral_of_open_connected_baseChange M j κ
  have : GeometricallyIntegral (constantBaseChangeCompactificationStructure k E M.toBase) :=
    inferInstanceAs (GeometricallyIntegral
      (pullback.fst (originalConstantFieldCover k E).hom M.toBase))
  exact GeometricallyIntegral.isIntegral_of_subsingleton
    (constantBaseChangeCompactificationStructure k E M.toBase)

/-- Package the actual constant pullback as its own curve model over `E`. -/
def constantCoverCurveModel :
    let : IsIntegral (constantBaseChangeCompactification k E M.toBase) :=
      constantCoverModel_isIntegral M j κ E
    let : Algebra E (constantBaseChangeCompactification k E M.toBase).functionField :=
      (baseToFunctionField (constantBaseChangeCompactificationStructure k E M.toBase)).toAlgebra
    CurveModel E (constantBaseChangeCompactification k E M.toBase).functionField := by
  intro instIntegral instAlgebra
  have : SmoothOfRelativeDimension 1
      (constantBaseChangeCompactificationStructure k E M.toBase) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
      (IsPullback.of_hasPullback (originalConstantFieldCover k E).hom M.toBase).flip
      (CurveModel.smooth M)
  exact literalCurveModel (constantBaseChangeCompactificationStructure k E M.toBase)

end AnabelianGeometry.FiniteField
