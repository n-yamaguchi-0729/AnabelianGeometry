/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.ConstantBaseFieldRange
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.FiniteRationalCoordinate
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.FiniteBoundarySplitting
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.GenusZeroParameter
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
import Nyll.AlgebraicCurves.Models.FunctionFields.CurveModelIsoFunctionField
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineRatFuncModel
import Nyll.AlgebraicCurves.Models.Points.InfinitePlace
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! # A finite splitting field for an actual genus-zero curve

A geometric rational coordinate and the finitely many coefficients of the
original function field give a finite Galois field of constants. The actual
base-change function field has precisely that compositum as its image, so the
smooth proper curve itself becomes the projective line over that finite field.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.ProjSpace

namespace AnabelianGeometry.GeometricFundamentalGroup

variable {k Ω F : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    [Field F] [Algebra Ω F] [Algebra k F] [IsScalarTower k Ω F]
    (M : CurveModel Ω F) {C : Scheme} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (e : M.C ≅ pullback c (specMap k Ω))
    (he : e.hom ≫ pullback.snd c (specMap k Ω) = M.toBase)

include M e he

/-- A geometric rational parameter descends far enough to split the actual
curve over a finite Galois extension. No rational model over that finite field
is included in the hypotheses. -/
theorem exists_finiteGalois_projectiveLine_model_of_parameter_above
    (z : F) (htr : Transcendental Ω z)
    (hz : IntermediateField.adjoin Ω ({z} : Set F) = ⊤)
    (D : FiniteGaloisIntermediateField k Ω) :
    ∃ E : FiniteGaloisIntermediateField k Ω, D ≤ E ∧
      ∃ I : pullback c (specMap k E) ≅ (projectiveLineRatFuncModel E).C,
        I.hom ≫ (projectiveLineRatFuncModel E).toBase =
          pullback.snd c (specMap k E) := by
  have smooth : Smooth c := SmoothOfRelativeDimension.smooth (n := 1) (f := c)
  let alg₀ : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
  let j₀ : C.functionField →ₐ[k] F :=
    { M.constantBaseEmbedding c e with
      commutes' := fun a => (M.constantBaseEmbedding_constants c e he a).trans
        (IsScalarTower.algebraMap_apply k Ω F a).symm }
  let A : IntermediateField k F := j₀.fieldRange
  have hfg₀ : Algebra.EssFiniteType k C.functionField :=
    essFiniteType_functionField c
  have hfgA : Algebra.EssFiniteType k A :=
    Algebra.EssFiniteType.of_surjective j₀.equivFieldRange.toAlgHom
      j₀.equivFieldRange.surjective
  have hA : A.FG := IntermediateField.essFiniteType_iff.mp hfgA
  have hgen : IntermediateField.adjoin A (Set.range (algebraMap Ω F)) = ⊤ := by
    apply top_unique
    intro x _hx
    have hx : x ∈ IntermediateField.adjoin Ω
        (Set.range (M.constantBaseEmbedding c e)) := by
      rw [M.adjoin_constantBaseEmbedding_eq_top c e he]
      exact IntermediateField.mem_top
    refine IntermediateField.adjoin_induction Ω (p := fun x _ =>
      x ∈ IntermediateField.adjoin A (Set.range (algebraMap Ω F)))
      ?_ ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, rfl⟩
      exact (IntermediateField.adjoin A (Set.range (algebraMap Ω F))).algebraMap_mem
        ⟨j₀ a, ⟨a, rfl⟩⟩
    · intro a
      exact IntermediateField.subset_adjoin A _ ⟨a, rfl⟩
    · intro x y _hx _hy hx hy
      exact IntermediateField.add_mem _ hx hy
    · intro x _hx hx
      exact IntermediateField.inv_mem _ hx
    · intro x y _hx _hy hx hy
      exact IntermediateField.mul_mem _ hx hy
  obtain ⟨E, hDE, ⟨φ⟩, hE⟩ := exists_finiteGalois_ratFunc_coordinate_above
    k Ω F A hA hgen z htr hz D
  let CE := pullback c (specMap k E)
  let cE := pullback.snd c (specMap k E)
  let algE : Algebra E CE.functionField := (baseToFunctionField cE).toAlgebra
  let ME : CurveModel E CE.functionField := CurveModel.ofSmoothProperCurve cE
  let j : CE.functionField →ₐ[E] F := constantTowerFieldEmbedding M c e he E
  have hA' : IntermediateField.adjoin k (Set.range (M.constantBaseEmbedding c e)) = A := by
    change IntermediateField.adjoin k (A : Set F) = A
    exact IntermediateField.adjoin_self k A
  have hB : (IsScalarTower.toAlgHom k E F).fieldRange =
      IntermediateField.adjoin k
        ((algebraMap Ω F) '' (E.toIntermediateField : Set Ω)) := by
    have himage : (algebraMap Ω F) '' (E.toIntermediateField : Set Ω) =
        ((IsScalarTower.toAlgHom k E F).fieldRange : Set F) := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a.val, a.property, rfl⟩
    rw [himage, IntermediateField.adjoin_self]
  have hj : j.fieldRange = IntermediateField.adjoin E ({z} : Set F) := by
    apply IntermediateField.restrictScalars_injective k
    rw [constantTowerFieldEmbedding_fieldRange M c e he E, hA', hB, hE]
  let ψ : CE.functionField ≃ₐ[E] RatFunc E :=
    j.equivFieldRange.trans ((IntermediateField.equivOfEq hj).trans φ.symm)
  obtain ⟨I, hI, _hfield⟩ :=
    CurveModel.exists_iso_comp_toBase_eq_functionFieldMap_eq ψ ME
      (projectiveLineRatFuncModel E)
  exact ⟨E, hDE, I, hI⟩

/-- The same construction without a prescribed finite constant subfield. -/
theorem exists_finiteGalois_projectiveLine_model_of_parameter
    (z : F) (htr : Transcendental Ω z)
    (hz : IntermediateField.adjoin Ω ({z} : Set F) = ⊤) :
    ∃ E : FiniteGaloisIntermediateField k Ω,
      ∃ I : pullback c (specMap k E) ≅ (projectiveLineRatFuncModel E).C,
        I.hom ≫ (projectiveLineRatFuncModel E).toBase =
          pullback.snd c (specMap k E) := by
  obtain ⟨E, _hbot, hE⟩ := exists_finiteGalois_projectiveLine_model_of_parameter_above
    M c e he z htr hz ⊥
  exact ⟨E, hE⟩

/-- A smooth proper geometrically integral curve of geometric genus zero
becomes the actual projective line over a finite Galois extension of constants. -/
theorem exists_finiteGalois_projectiveLine_model_of_genus_zero_above
    [IsAlgClosed Ω] [IsCurveOver Ω F] [Algebra.EssFiniteType Ω F]
    (hg : genusFF Ω F = 0) (D : FiniteGaloisIntermediateField k Ω) :
    ∃ E : FiniteGaloisIntermediateField k Ω, D ≤ E ∧
      ∃ I : pullback c (specMap k E) ≅ (projectiveLineRatFuncModel E).C,
        I.hom ≫ (projectiveLineRatFuncModel E).toBase =
          pullback.snd c (specMap k E) := by
  classical
  have : Infinite (Place Ω F) := M.infinite_place
  obtain ⟨v₀, vInfty, hne⟩ := exists_pair_ne (Place Ω F)
  obtain ⟨z, _hz, htr, hgen, _hdiv⟩ := exists_parameter_of_genus_zero hg v₀ vInfty hne
  exact exists_finiteGalois_projectiveLine_model_of_parameter_above M c e he z htr hgen D

/-- Geometric genus zero implies splitting over some finite Galois extension. -/
theorem exists_finiteGalois_projectiveLine_model_of_genus_zero
    [IsAlgClosed Ω] [IsCurveOver Ω F] [Algebra.EssFiniteType Ω F]
    (hg : genusFF Ω F = 0) :
    ∃ E : FiniteGaloisIntermediateField k Ω,
      ∃ I : pullback c (specMap k E) ≅ (projectiveLineRatFuncModel E).C,
        I.hom ≫ (projectiveLineRatFuncModel E).toBase =
          pullback.snd c (specMap k E) := by
  obtain ⟨E, _hbot, hE⟩ := exists_finiteGalois_projectiveLine_model_of_genus_zero_above
    M c e he hg ⊥
  exact ⟨E, hE⟩

/-- The same finite Galois extension can split the curve and define a
specified finite family of geometric points. The point maps into the actual
base-changed curve, not just abstract labels, are retained. -/
theorem exists_finiteGalois_projectiveLine_model_and_points_above
    [IsAlgClosed Ω] [IsCurveOver Ω F] [Algebra.EssFiniteType Ω F]
    (hg : genusFF Ω F = 0) (D : FiniteGaloisIntermediateField k Ω)
    {ι : Type} [Finite ι]
    (p : ι → (Spec (.of Ω) ⟶ C))
    (hp : ∀ i, p i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    ∃ E : FiniteGaloisIntermediateField k Ω, D ≤ E ∧
      ∃ I : pullback c (specMap k E) ≅ (projectiveLineRatFuncModel E).C,
        I.hom ≫ (projectiveLineRatFuncModel E).toBase =
          pullback.snd c (specMap k E) ∧
        ∃ q : ι → (Spec (.of E) ⟶ pullback c (specMap k E)),
          (∀ i, q i ≫ pullback.snd c (specMap k E) = 𝟙 _) ∧
          ∀ i, Spec.map (CommRingCat.ofHom E.toIntermediateField.val.toRingHom) ≫
            q i ≫ pullback.fst c (specMap k E) = p i := by
  have smooth : Smooth c := SmoothOfRelativeDimension.smooth (n := 1) (f := c)
  obtain ⟨D₀, hfin, hgal, q₀, hq₀, hpoint₀⟩ :=
    exists_finiteGalois_field_of_point_family k Ω c p hp
  let Dp : FiniteGaloisIntermediateField k Ω :=
    { D₀ with finiteDimensional := hfin, isGalois := hgal }
  obtain ⟨E, hDE, I, hI⟩ :=
    exists_finiteGalois_projectiveLine_model_of_genus_zero_above M c e he hg (D ⊔ Dp)
  let j : D₀ →ₐ[k] E := IntermediateField.inclusion
    ((FiniteGaloisIntermediateField.le_iff Dp E).mp (le_sup_right.trans hDE))
  let qE (i : ι) : Spec (.of E) ⟶ C :=
    Spec.map (CommRingCat.ofHom j.toRingHom) ≫ q₀ i
  have hqE (i : ι) : qE i ≫ c = specMap k E := by
    change (Spec.map (CommRingCat.ofHom j.toRingHom) ≫ q₀ i) ≫ c = _
    rw [Category.assoc, hq₀, ← Spec.map_comp]
    congr 1
  let q (i : ι) : Spec (.of E) ⟶ pullback c (specMap k E) :=
    pullback.lift (qE i) (𝟙 _) ((hqE i).trans (Category.id_comp _).symm)
  refine ⟨E, le_sup_left.trans hDE, I, hI, q, ?_, ?_⟩
  · intro i
    exact pullback.lift_snd _ _ _
  · intro i
    rw [pullback.lift_fst]
    change Spec.map (CommRingCat.ofHom E.toIntermediateField.val.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom j.toRingHom) ≫ q₀ i) = p i
    rw [← Category.assoc, ← Spec.map_comp]
    exact hpoint₀ i

/-- Simultaneous splitting of the curve and a finite point family, with no
prescribed lower bound on the finite constant field. -/
theorem exists_finiteGalois_projectiveLine_model_and_points
    [IsAlgClosed Ω] [IsCurveOver Ω F] [Algebra.EssFiniteType Ω F]
    (hg : genusFF Ω F = 0) {ι : Type} [Finite ι]
    (p : ι → (Spec (.of Ω) ⟶ C))
    (hp : ∀ i, p i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    ∃ E : FiniteGaloisIntermediateField k Ω,
      ∃ I : pullback c (specMap k E) ≅ (projectiveLineRatFuncModel E).C,
        I.hom ≫ (projectiveLineRatFuncModel E).toBase =
          pullback.snd c (specMap k E) ∧
        ∃ q : ι → (Spec (.of E) ⟶ pullback c (specMap k E)),
          (∀ i, q i ≫ pullback.snd c (specMap k E) = 𝟙 _) ∧
          ∀ i, Spec.map (CommRingCat.ofHom E.toIntermediateField.val.toRingHom) ≫
            q i ≫ pullback.fst c (specMap k E) = p i := by
  obtain ⟨E, _hbot, hE⟩ := exists_finiteGalois_projectiveLine_model_and_points_above
    M c e he hg ⊥ p hp
  exact ⟨E, hE⟩

end AnabelianGeometry.GeometricFundamentalGroup
