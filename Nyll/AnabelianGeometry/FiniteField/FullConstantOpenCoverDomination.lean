/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.CompactifiedOpenCoverBoundary
public import Nyll.EtaleFundamentalGroups.GaloisCovers.CompactificationDiagram
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FullConstantCompactification

/-!
# Full constants and boundary growth for open covering towers

An actual transition of connected finite étale open covers extends to their
normalization compactifications, even when ramified at infinity. The larger
cover's full constants embed compatibly with those of the dominated cover.
On that single geometric component its boundary cannot shrink.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.FiniteField

/-- An actual domination of open covers produces compatible full constants
on the larger cover's original normalization, retaining its native generic
source and bounding its geometric boundary on one full-constant component. -/
theorem exists_fullConstants_open_cover_boundary_domination
    {k F : Type} [Field k] [Finite k] [Field F] [Algebra k F]
    (L κ : Type) [Field L] [Field κ] [IsAlgClosed κ]
    [Algebra k L] [FiniteDimensional k L]
    [Algebra k κ] [Algebra L κ] [IsScalarTower k L κ]
    (M : CurveModel k F) {X : Scheme}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (A D : FiniteEtale X) [IsConnected A] [IsConnected D]
    (cA : (connectedCoverGenericComposite A ≫ j).normalization ⟶ Spec (.of L))
    [IsProper cA] [SmoothOfRelativeDimension 1 cA] [GeometricallyIntegral cA]
    (hcA : cA ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
      (connectedCoverGenericComposite A ≫ j).fromNormalization ≫ M.toBase)
    (t : D ⟶ A) :
    let _ : IsIntegral D.left := isIntegral_left_of_isConnected_finiteEtale D
    let cD : D.left ⟶ Spec (.of k) := D.hom ≫ j ≫ M.toBase
    let _ : Algebra k D.left.functionField := (baseToFunctionField cD).toAlgebra
    let E := algebraicClosure k D.left.functionField
    let q := connectedCoverGenericComposite D ≫ j
    let i := connectedCoverCompactificationInclusion j D
    let d := connectedCoverCompactificationMap j t
    Finite E ∧ ∃ (cE : q.normalization ⟶ Spec (.of E))
      (φ : L →ₐ[k] E) (σ : E →ₐ[k] κ),
      cE ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) =
        q.fromNormalization ≫ M.toBase ∧
      IsProper cE ∧ SmoothOfRelativeDimension 1 cE ∧ GeometricallyIntegral cE ∧
      SmoothOfRelativeDimension 1 (i ≫ cE) ∧ GeometricallyIntegral (i ≫ cE) ∧
      (i ≫ cE) ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) = cD ∧
      q.toNormalization ≫ cE =
        Spec.map (CommRingCat.ofHom (algebraMap E D.left.functionField)) ∧
      d ≫ cA = cE ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ∧
      (∀ a : L, σ (φ a) = algebraMap L κ a) ∧
      let _ : Algebra E κ := σ.toRingHom.toAlgebra
      Nat.card (GeometricBoundaryPoint L κ cA
        (connectedCoverCompactificationInclusion j A)) ≤
        Nat.card (GeometricBoundaryPoint E κ cE i) := by
  intro hD cD algD E q i d
  have : IsIntegral A.left := isIntegral_left_of_isConnected_finiteEtale A
  obtain ⟨N, dN, hdN, _, e, he, hegen⟩ :=
    exists_curveModel_iso_open_cover_normalization_with_generic_of_perfectField M j D
  let cL : N.C ⟶ Spec (.of L) := e.inv ≫ d ≫ cA
  have hcL : cL ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) = N.toBase := by
    dsimp only [cL]
    rw [Category.assoc, Category.assoc, hcA, ← Category.assoc d,
      connectedCoverCompactificationMap_fromNormalization]
    exact (congrArg
      (fun f : q.normalization ⟶ M.C => e.inv ≫ (f ≫ M.toBase)) he.symm).trans
        ((congrArg (fun f : q.normalization ⟶ Spec (.of k) => e.inv ≫ f)
          (Category.assoc e.hom dN M.toBase)).trans
            ((e.inv_hom_id_assoc (dN ≫ M.toBase)).trans hdN))
  obtain ⟨hE, cN, φ, σ, hcN, hproper, hsmooth, hgeom, hgen, hL, hσ⟩ :=
    N.exists_fullConstants_structure_compatible (κ := κ) cL hcL
  have : Finite E := hE
  let cE : q.normalization ⟶ Spec (.of E) := e.hom ≫ cN
  have hcbase : cE ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) =
      q.fromNormalization ≫ M.toBase := by
    change (e.hom ≫ cN) ≫ _ = _
    rw [Category.assoc, hcN, ← hdN, ← Category.assoc, he]
  have hcproper : IsProper cE := by dsimp only [cE]; infer_instance
  have hcsmooth : SmoothOfRelativeDimension 1 cE :=
    smoothOfRelativeDimension_comp 0 1 e.hom cN
  have hcgeom : GeometricallyIntegral cE := by
    have : MorphismProperty.RespectsIso
        (@GeometricallyIntegral : MorphismProperty Scheme) := by
      rw [GeometricallyIntegral.eq_geometrically, geometrically_eq_universally]
      exact MorphismProperty.universally_respectsIso _
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := (@GeometricallyIntegral : MorphismProperty Scheme)) e.hom cN).mpr hgeom
  have hopenSmooth : SmoothOfRelativeDimension 1 (i ≫ cE) :=
    smoothOfRelativeDimension_comp 0 1 i cE
  have hopenGeom : GeometricallyIntegral (i ≫ cE) :=
    GeometricallyIntegral.comp_of_isOpenImmersion i cE
  have hopenBase : (i ≫ cE) ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) = cD := by
    rw [Category.assoc, hcbase, ← Category.assoc,
      connectedCoverCompactificationInclusion_comp, Category.assoc]
  have hgeneric : q.toNormalization ≫ cE =
      Spec.map (CommRingCat.ofHom (algebraMap E D.left.functionField)) := by
    change q.toNormalization ≫ (e.hom ≫ cN) = _
    exact (Category.assoc q.toNormalization e.hom cN).symm.trans
      ((congrArg (fun f : Spec (.of D.left.functionField) ⟶ N.C => f ≫ cN) hegen).trans hgen)
  have hstruct : d ≫ cA = cE ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    change d ≫ cA = (e.hom ≫ cN) ≫ _
    rw [Category.assoc, ← hL]
    exact (e.hom_inv_id_assoc (d ≫ cA)).symm
  refine ⟨hE, cE, φ, σ, hcbase, hcproper, hcsmooth, hcgeom,
    hopenSmooth, hopenGeom, hopenBase, hgeneric, hstruct, hσ, ?_⟩
  intro coefficientAlgebra
  have : IsScalarTower k E κ :=
    IsScalarTower.of_algebraMap_eq (fun a => (σ.commutes a).symm)
  have hcoeff : Spec.map (CommRingCat.ofHom (algebraMap E κ)) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) =
        Spec.map (CommRingCat.ofHom (algebraMap L κ)) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    ext a
    exact hσ a
  have hAbase : (connectedCoverCompactificationInclusion j A ≫ cA) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k L)) = A.hom ≫ (j ≫ M.toBase) := by
    rw [Category.assoc, hcA, ← Category.assoc,
      connectedCoverCompactificationInclusion_comp, Category.assoc]
  exact boundaryCard_le_of_compactified_open_cover_domination k E L κ
    (j ≫ M.toBase) D A cE cA i (connectedCoverCompactificationInclusion j A)
    hopenBase hAbase t d (connectedCoverCompactificationInclusion_naturality j t)
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) hcoeff hstruct
    (connectedCoverCompactificationMap_mem_boundary_iff j t)

end AnabelianGeometry.FiniteField
