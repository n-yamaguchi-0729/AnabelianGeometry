/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.PerfectOpenCoverModel
public import Nyll.AlgebraicCurves.Models.Construction.FullConstantStructure
public import Nyll.SchemeTheory.FunctionFields.GeometricIntegrality

/-!
# Full constants on the actual covering compactification

The normalization containing the original connected finite étale cover is
smooth, proper and geometrically integral over the relative algebraic
closure of the perfect ground field in that cover's own function field.
The same full-constant structure restricts to the original open cover.
Its coefficient map at the original generic source is the literal field
inclusion, and both original structural maps over the ground field remain
unchanged.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

/-- Rebase the actual normalization compactification and its original open
cover onto the full constants of the original cover function field. No
replacement cover, geometric connectedness premise, or independently
chosen coefficient marking is introduced. -/
theorem connectedCoverCompactification_exists_fullConstants_structure_of_perfectField
    {k F : Type} [Field k] [PerfectField k] [Field F] [Algebra k F]
    (M : CurveModel k F) {X : Scheme}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (W : FiniteEtale X) [IsConnected W] :
    let _ : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let cW : W.left ⟶ Spec (.of k) := W.hom ≫ j ≫ M.toBase
    let _ : Algebra k W.left.functionField := (baseToFunctionField cW).toAlgebra
    let E := algebraicClosure k W.left.functionField
    let φ := Spec.map (CommRingCat.ofHom (algebraMap k E))
    let q := FiniteEtale.connectedCoverGenericComposite W ≫ j
    let i := FiniteEtale.connectedCoverCompactificationInclusion j W
    Module.Finite k E ∧ ∃ c : q.normalization ⟶ Spec (.of E),
      c ≫ φ = q.fromNormalization ≫ M.toBase ∧
      IsProper c ∧ SmoothOfRelativeDimension 1 c ∧ GeometricallyIntegral c ∧
      SmoothOfRelativeDimension 1 (i ≫ c) ∧ GeometricallyIntegral (i ≫ c) ∧
      (i ≫ c) ≫ φ = cW ∧
      q.toNormalization ≫ c =
        Spec.map (CommRingCat.ofHom (algebraMap E W.left.functionField)) := by
  intro hIntegral cW algW E φ q i
  obtain ⟨N, d, hd, _, e, he, hegen⟩ :=
    exists_curveModel_iso_open_cover_normalization_with_generic_of_perfectField M j W
  obtain ⟨hE, cN, hcN, hproper, hsmooth, hgeom, hgen⟩ :=
    N.exists_fullConstants_structure_of_perfectField
  let c : q.normalization ⟶ Spec (.of E) := e.hom ≫ cN
  have hcbase : c ≫ φ = q.fromNormalization ≫ M.toBase := by
    change (e.hom ≫ cN) ≫ φ = _
    rw [Category.assoc, hcN, ← hd, ← Category.assoc, he]
  have hcproper : IsProper c := by dsimp only [c]; infer_instance
  have hcsmooth : SmoothOfRelativeDimension 1 c :=
    smoothOfRelativeDimension_comp 0 1 e.hom cN
  have : MorphismProperty.RespectsIso
      (@GeometricallyIntegral : MorphismProperty Scheme) := by
    rw [GeometricallyIntegral.eq_geometrically, geometrically_eq_universally]
    exact MorphismProperty.universally_respectsIso _
  have hcgeom : GeometricallyIntegral c :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyIntegral) e.hom cN).mpr hgeom
  have hopenSmooth : SmoothOfRelativeDimension 1 (i ≫ c) :=
    smoothOfRelativeDimension_comp 0 1 i c
  have hopenGeom : GeometricallyIntegral (i ≫ c) :=
    GeometricallyIntegral.comp_of_isOpenImmersion i c
  refine ⟨hE, c, hcbase, hcproper, hcsmooth, hcgeom,
    hopenSmooth, hopenGeom, ?_, ?_⟩
  · rw [Category.assoc, hcbase, ← Category.assoc,
      FiniteEtale.connectedCoverCompactificationInclusion_comp, Category.assoc]
  · change q.toNormalization ≫ (e.hom ≫ cN) = _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun r => r ≫ cN) hegen).trans hgen)

/-- The finite-field specialization retains finiteness as a set while
using the same original cover, normalization and coefficient inclusion. -/
theorem connectedCoverCompactification_exists_fullConstants_structure
    {k F : Type} [Field k] [Finite k] [Field F] [Algebra k F]
    (M : CurveModel k F) {X : Scheme}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (W : FiniteEtale X) [IsConnected W] :
    let _ : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let cW : W.left ⟶ Spec (.of k) := W.hom ≫ j ≫ M.toBase
    let _ : Algebra k W.left.functionField := (baseToFunctionField cW).toAlgebra
    let E := algebraicClosure k W.left.functionField
    let φ := Spec.map (CommRingCat.ofHom (algebraMap k E))
    let q := FiniteEtale.connectedCoverGenericComposite W ≫ j
    let i := FiniteEtale.connectedCoverCompactificationInclusion j W
    Finite E ∧ ∃ c : q.normalization ⟶ Spec (.of E),
      c ≫ φ = q.fromNormalization ≫ M.toBase ∧
      IsProper c ∧ SmoothOfRelativeDimension 1 c ∧ GeometricallyIntegral c ∧
      SmoothOfRelativeDimension 1 (i ≫ c) ∧ GeometricallyIntegral (i ≫ c) ∧
      (i ≫ c) ≫ φ = cW ∧
      q.toNormalization ≫ c =
        Spec.map (CommRingCat.ofHom (algebraMap E W.left.functionField)) := by
  intro hIntegral cW algW E φ q i
  obtain ⟨hfinite, c, hbase, hproper, hsmooth, hgeom, hopenSmooth, hopenGeom, hcover, hgeneric⟩ :=
    connectedCoverCompactification_exists_fullConstants_structure_of_perfectField M j W
  have : Module.Finite k E := hfinite
  exact ⟨Module.finite_of_finite k, c, hbase, hproper, hsmooth, hgeom,
    hopenSmooth, hopenGeom, hcover, hgeneric⟩

end EtaleFundamentalGroups
