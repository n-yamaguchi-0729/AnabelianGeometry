/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.LocalGeometry.RationalSectionCenters
public import Nyll.AlgebraicCurves.Geometry.Curves.GeometricGenusClosureComparison
public import Nyll.EtaleFundamentalGroups.GaloisCovers.ConstantBaseChangeCompactification
public import Nyll.AnabelianGeometry.GeometricFundamentalGroup.FiniteGenusZeroModel
public import Nyll.AlgebraicCurves.Models.Rational.RationalBoundaryConfigurationIso
public import Nyll.AlgebraicCurves.Models.Sections.RationalSectionBoundaryPlace
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Mathlib.Data.Fintype.EquivFin

/-!
# An actual finite constant model for genus-zero separation

The original geometric boundary is counted by its actual morphisms from the
specified constant closure. Three such points, the genus-zero coordinate and
an arbitrary prescribed finite constant field descend together. The resulting
projective-line isomorphism keeps the source of the original constant cover
and its two original projections.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.ProjSpace AlgebraicCurve
open TopologicalSpace NeronModelInfra

namespace AnabelianGeometry.FiniteField

attribute [local instance] AlgebraicCurve.CurveModel.isIntegral
  AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.smooth

/-- The actual geometric boundary points of the original open immersion,
with their embeddings in the prescribed closure retained. -/
abbrev GeometricBoundaryPoint
    (k κ : Type u) [Field k] [Field κ] [Algebra k κ]
    {X U : Scheme.{u}} (c : X ⟶ Spec (.of k)) (j : U ⟶ X) :=
  {p : SchemeHomOver (Spec.algebraMap k κ) c //
    p.val (IsLocalRing.closedPoint κ) ∉ Set.range j}

/-- Every actual rational section of the literal projective line has a
coordinate over the unchanged ground field. -/
theorem exists_projectiveRationalPoint_of_section
    (k : Type u) [Field k]
    (p : Spec (.of k) ⟶ (projectiveLineRatFuncModel k).C)
    (hp : p ≫ (projectiveLineRatFuncModel k).toBase = 𝟙 _) :
    ∃ a : Projectivization k (k × k),
      p (IsLocalRing.closedPoint k) = projectiveRationalPoint a := by
  let M := projectiveLineRatFuncModel k
  have : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id M.toBase p hp
  have hrange : Set.range p = {p (IsLocalRing.closedPoint k)} :=
    Set.range_eq_singleton_iff.mpr fun t => congrArg p (Subsingleton.elim _ _)
  have hclosed : IsClosed {p (IsLocalRing.closedPoint k)} := by
    rw [← hrange]
    exact p.isClosedEmbedding.isClosed_range
  let x : closedPoints M.C := ⟨p (IsLocalRing.closedPoint k), hclosed⟩
  have hrat := M.isRational_placeOfPoint_of_section p hp x rfl
  obtain ⟨a, ha⟩ := exists_projectiveRationalPoint_of_isRational k (M.placeOfPoint x) hrat
  exact ⟨a, (congrArg Subtype.val (M.placeOfPoint_bijective.1 ha)).symm⟩

/-- Genus zero and the original geometric boundary construct a literal
projective-line compactification of the actual finite constant cover, with
three omitted rational points. No model isomorphism is an input. -/
theorem exists_genusZero_constantModel_above
    (k κ : Type u) [Field k] [Finite k] [Field κ]
    [Algebra k κ] [IsAlgClosed κ] [IsSepClosure k κ]
    {X U : Scheme.{u}} [IsIntegral X]
    (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    [GeometricallyIntegral c] (j : U ⟶ X) [IsOpenImmersion j]
    (hg : geometricGenus k c = 0)
    (hboundary : 2 < Nat.card (GeometricBoundaryPoint k κ c j))
    (D : FiniteGaloisIntermediateField k κ) :
    ∃ E : FiniteGaloisIntermediateField k κ, D ≤ E ∧
      let _ : IsFiniteEtale (Spec.algebraMap k E) := constantField_specMap_isFiniteEtale k E
      ∃ I : constantBaseChangeCompactification k E c ≅ (projectiveLineRatFuncModel E).C,
        I.hom ≫ (projectiveLineRatFuncModel E).toBase =
          constantBaseChangeCompactificationStructure k E c ∧
        ∃ s : Finset (Projectivization E (E × E)),
          2 < s.card ∧ ∀ a ∈ s, projectiveRationalPoint a ∉
            Set.range (constantBaseChangeOpen k E c j ≫ I.hom) := by
  classical
  let B := GeometricBoundaryPoint k κ c j
  have : Finite B := Nat.finite_of_card_ne_zero
    (ne_of_gt (lt_trans (by decide : 0 < 2) hboundary))
  let : Fintype B := Fintype.ofFinite B
  have hthree : Fintype.card (Fin 3) ≤ Fintype.card B := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact hboundary
  obtain ⟨b : Fin 3 ↪ B⟩ := Function.Embedding.nonempty_of_card_le hthree
  let Cκ := pullback c (specMap k κ)
  let cκ := baseChange k c κ
  let F := Cκ.functionField
  let : Algebra κ F := (baseToFunctionField cκ).toAlgebra
  let : Algebra k F := ((algebraMap κ F).comp (algebraMap k κ)).toAlgebra
  have : IsScalarTower k κ F := IsScalarTower.of_algebraMap_eq' rfl
  have : IsCurveOver κ F := isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
    cκ (RingEquiv.refl F) (fun _ => rfl)
  have : Algebra.EssFiniteType κ F := essFiniteType_functionField cκ
  let M := CurveModel.ofSmoothProperCurve cκ
  have hgκ : genusFF κ F = 0 :=
    (geometricGenus_eq_genusFF_baseChange k c κ).symm.trans hg
  let p (i : Fin 3) : Spec (.of κ) ⟶ X := (b i).val.val
  have hp (i : Fin 3) : p i ≫ c = specMap k κ := (b i).val.property
  obtain ⟨E, hDE, I, hI, q, hq, hpoint⟩ :=
    GeometricFundamentalGroup.exists_finiteGalois_projectiveLine_model_and_points_above
      M c (Iso.refl Cκ) (Category.id_comp cκ) hgκ D p hp
  have : IsFiniteEtale (Spec.algebraMap k E) := constantField_specMap_isFiniteEtale k E
  let a := (originalConstantFieldCover k E).hom
  let eC := pullbackSymmetry a c
  let I' := eC ≪≫ I
  have hI' : I'.hom ≫ (projectiveLineRatFuncModel E).toBase =
      constantBaseChangeCompactificationStructure k E c := by
    change (eC.hom ≫ I.hom) ≫ _ = _
    exact (Category.assoc eC.hom I.hom _).trans
      ((congrArg (fun t => eC.hom ≫ t) hI).trans
        (pullbackSymmetry_hom_comp_snd a c))
  have hqP (i : Fin 3) : (q i ≫ I.hom) ≫ (projectiveLineRatFuncModel E).toBase = 𝟙 _ := by
    rw [Category.assoc, hI, hq i]
  choose label hlabel using fun i =>
    exists_projectiveRationalPoint_of_section E (q i ≫ I.hom) (hqP i)
  have hinj : Function.Injective label := by
    intro i i' heq
    have hcenter : (q i ≫ I.hom) (IsLocalRing.closedPoint E) =
        (q i' ≫ I.hom) (IsLocalRing.closedPoint E) :=
      (hlabel i).trans ((congrArg projectiveRationalPoint heq).trans (hlabel i').symm)
    have hhom := Scheme.rationalSections_eq_of_center_eq
      (projectiveLineRatFuncModel E).toBase (q i ≫ I.hom) (q i' ≫ I.hom)
      (hqP i) (hqP i') hcenter
    have hqq : q i = q i' := (cancel_mono I.hom).mp hhom
    apply b.injective
    apply Subtype.ext
    apply Subtype.ext
    change p i = p i'
    rw [← hpoint i, ← hpoint i', hqq]
  let s : Finset (Projectivization E (E × E)) := Finset.univ.image label
  have hs : 2 < s.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    exact Nat.lt_succ_self 2
  refine ⟨E, hDE, I', hI', s, hs, ?_⟩
  intro v hv
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  intro hmem
  obtain ⟨w, hw⟩ := hmem
  have hcenter : eC.hom (constantBaseChangeOpen k E c j w) =
      q i (IsLocalRing.closedPoint E) := by
    apply I.hom.isOpenEmbedding.injective
    exact hw.trans (hlabel i).symm
  have hpointE : pullback.fst c (specMap k E) (q i (IsLocalRing.closedPoint E)) =
      p i (IsLocalRing.closedPoint κ) := by
    have h := congrArg (fun t : Spec (.of κ) ⟶ X => t (IsLocalRing.closedPoint κ)) (hpoint i)
    change pullback.fst c (specMap k E)
      (q i ((Spec.map (CommRingCat.ofHom E.toIntermediateField.val.toRingHom))
        (IsLocalRing.closedPoint κ))) = _ at h
    rw [show (Spec.map (CommRingCat.ofHom E.toIntermediateField.val.toRingHom))
      (IsLocalRing.closedPoint κ) = IsLocalRing.closedPoint E from Subsingleton.elim _ _] at h
    exact h
  apply (b i).property
  refine ⟨((FiniteEtale.pullback (j ≫ c)).obj (originalConstantFieldCover k E)).hom w, ?_⟩
  calc
    j (((FiniteEtale.pullback (j ≫ c)).obj (originalConstantFieldCover k E)).hom w) =
        ((FiniteEtale.pullback c).obj (originalConstantFieldCover k E)).hom
          (constantBaseChangeOpen k E c j w) :=
      (congrArg (fun t => t w) (constantBaseChangeOpen_original k E c j)).symm
    _ = pullback.fst c (specMap k E) (eC.hom (constantBaseChangeOpen k E c j w)) :=
      (congrArg (fun t => t (constantBaseChangeOpen k E c j w))
        (pullbackSymmetry_hom_comp_fst a c)).symm
    _ = pullback.fst c (specMap k E) (q i (IsLocalRing.closedPoint E)) :=
      congrArg (pullback.fst c (specMap k E)) hcenter
    _ = p i (IsLocalRing.closedPoint κ) := hpointE

end AnabelianGeometry.FiniteField
