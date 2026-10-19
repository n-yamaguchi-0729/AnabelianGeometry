/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.FiniteGenusZeroModel
import Nyll.AlgebraicCurves.Models.Rational.RationalBoundaryConfigurationIso
import Nyll.AlgebraicCurves.Models.Ramification.OpenBoundary
import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearTower
import Nyll.AlgebraicCurves.Models.Sections.RationalSectionBoundaryPlace
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # An actual split model of an open genus-zero curve

The finite field is chosen using all geometric boundary points. Surjectivity
of extension of constants then shows that every boundary point of the finite
model is the image of one of the descended sections. The actual finite open
is therefore a literal rational-configuration open.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.ProjSpace TopologicalSpace

namespace AnabelianGeometry.GeometricFundamentalGroup

attribute [local instance] CurveModel.isProper CurveModel.isIntegral CurveModel.smooth

/-- A nonempty open in a geometrically genus-zero proper curve has a literal
rational-configuration model after finite Galois extension. The ambient and
structural morphism equations are retained, and rationality of the boundary
is a conclusion of the construction. -/
theorem exists_finiteGalois_rationalConfiguration_model_above
    {k Ω F : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    [IsAlgClosed Ω] [Field F] [Algebra Ω F] [Algebra k F] [IsScalarTower k Ω F]
    [IsCurveOver Ω F] [Algebra.EssFiniteType Ω F]
    (M : CurveModel Ω F) {C : Scheme} [IsIntegral C]
    (c : C ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    [GeometricallyIntegral c]
    (e : M.C ≅ pullback c (specMap k Ω))
    (he : e.hom ≫ pullback.snd c (specMap k Ω) = M.toBase)
    (hg : genusFF Ω F = 0) (U : C.Opens) (hU : (U : Set C).Nonempty)
    (D : FiniteGaloisIntermediateField k Ω) :
    ∃ E : FiniteGaloisIntermediateField k Ω, D ≤ E ∧
      ∃ I : pullback c (specMap k E) ≅ (projectiveLineRatFuncModel E).C,
        I.hom ≫ (projectiveLineRatFuncModel E).toBase =
          pullback.snd c (specMap k E) ∧
        ∃ s : Finset (Projectivization E (E × E)),
          (∀ a, a ∈ s ↔ projectiveRationalPoint a ∉
            Set.range ((pullback.fst c (specMap k E) ⁻¹ᵁ U).ι ≫ I.hom)) ∧
          ∃ J : ((pullback.fst c (specMap k E) ⁻¹ᵁ U) : Scheme) ≅
              (rationalConfigurationOpen s : Scheme),
            J.hom ≫ (rationalConfigurationOpen s).ι =
              (pullback.fst c (specMap k E) ⁻¹ᵁ U).ι ≫ I.hom ∧
            J.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
              (pullback.fst c (specMap k E) ⁻¹ᵁ U).ι ≫
                pullback.snd c (specMap k E) := by
  classical
  have smooth : Smooth c := SmoothOfRelativeDimension.smooth (n := 1) (f := c)
  have surjΩ : Surjective (specMap k Ω) :=
    ⟨fun x => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ x⟩⟩
  let p₀ : M.C ⟶ C := e.hom ≫ pullback.fst c (specMap k Ω)
  have surj₀ : Surjective p₀ := inferInstance
  let UΩ : M.C.Opens := p₀ ⁻¹ᵁ U
  have nonemptyUΩ : Nonempty (UΩ : Scheme) := by
    obtain ⟨x, hx⟩ := hU
    obtain ⟨z, hz⟩ := p₀.surjective x
    exact ⟨⟨z, show p₀ z ∈ U from hz.symm ▸ hx⟩⟩
  let B := M.openBoundaryPlaces UΩ.ι
  let finiteB : Fintype B := (M.openBoundaryPlaces_finite UΩ.ι).fintype
  let pΩ (b : B) : Spec (.of Ω) ⟶ M.C :=
    pointOfClosedPoint M.toBase (M.placeEquiv.symm b.val).val
      (M.placeEquiv.symm b.val).property
  have hpΩ (b : B) : pΩ b ≫ M.toBase = 𝟙 _ :=
    pointOfClosedPoint_comp M.toBase (M.placeEquiv.symm b.val).val
      (M.placeEquiv.symm b.val).property
  have hpointΩ (b : B) : pΩ b (IsLocalRing.closedPoint Ω) =
      (M.placeEquiv.symm b.val).val :=
    pointOfClosedPoint_apply M.toBase (M.placeEquiv.symm b.val).val
      (M.placeEquiv.symm b.val).property _
  let p (b : B) : Spec (.of Ω) ⟶ C := pΩ b ≫ p₀
  have hp₀ : p₀ ≫ c = M.toBase ≫ specMap k Ω := by
    change (e.hom ≫ pullback.fst c (specMap k Ω)) ≫ c = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  have hp (b : B) : p b ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
    change (pΩ b ≫ p₀) ≫ c = _
    rw [Category.assoc, hp₀, ← Category.assoc, hpΩ b, Category.id_comp]
  obtain ⟨E, hDE, I, hI, q, hq, hpoint⟩ :=
    exists_finiteGalois_projectiveLine_model_and_points_above M c e he hg D p hp
  let CE := pullback c (specMap k E)
  let cE := pullback.snd c (specMap k E)
  let UE : CE.Opens := pullback.fst c (specMap k E) ⁻¹ᵁ U
  have surjE : Surjective (specMap k E) :=
    ⟨fun x => ⟨IsLocalRing.closedPoint E, Subsingleton.elim _ x⟩⟩
  have nonemptyUE : Nonempty (UE : Scheme) := by
    obtain ⟨x, hx⟩ := hU
    obtain ⟨y, hy⟩ := (pullback.fst c (specMap k E)).surjective x
    exact ⟨⟨y, show pullback.fst c (specMap k E) y ∈ U from hy.symm ▸ hx⟩⟩
  let eE := M.constantTowerModelIso k E Ω c e
  have heE := M.constantTowerModelIso_base k E Ω c e he
  let r : M.C ⟶ CE := eE.hom ≫ pullback.fst cE (specMap E Ω)
  have surjEΩ : Surjective (specMap E Ω) :=
    ⟨fun x => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ x⟩⟩
  have surjr : Surjective r := inferInstance
  have hr : r ≫ pullback.fst c (specMap k E) = p₀ := by
    change ((e.hom ≫ (Scheme.constantBaseChangeTowerIso k E Ω c).inv) ≫
      pullback.fst cE (specMap E Ω)) ≫ pullback.fst c (specMap k E) = _
    rw [Category.assoc, Category.assoc, ← Scheme.constantBaseChangeTowerIso_fst,
      (Scheme.constantBaseChangeTowerIso k E Ω c).inv_hom_id_assoc]
  have hrbase : r ≫ cE = M.toBase ≫ specMap E Ω := by
    change (eE.hom ≫ pullback.fst cE (specMap E Ω)) ≫ cE = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, heE]
  have hpointE (b : B) : pΩ b ≫ r = specMap E Ω ≫ q b := by
    apply pullback.hom_ext
    · rw [Category.assoc, hr, Category.assoc]
      exact (hpoint b).symm
    · rw [Category.assoc, hrbase, ← Category.assoc, hpΩ b,
        Category.id_comp, Category.assoc, hq b, Category.comp_id]
  have hcenterE (b : B) : r (M.placeEquiv.symm b.val).val =
      q b (IsLocalRing.closedPoint E) := by
    have h := congrArg (fun a : Spec (.of Ω) ⟶ CE => a (IsLocalRing.closedPoint Ω))
      (hpointE b)
    change r (pΩ b (IsLocalRing.closedPoint Ω)) =
      q b ((specMap E Ω) (IsLocalRing.closedPoint Ω)) at h
    rw [hpointΩ b] at h
    exact h.trans (congrArg (q b) (Subsingleton.elim _ (IsLocalRing.closedPoint E)))
  let MP := projectiveLineRatFuncModel E
  let j : (UE : Scheme) ⟶ MP.C := UE.ι ≫ I.hom
  have hboundary : ∀ V : MP.openBoundaryPlaces j, V.val.IsRational := by
    intro V
    let x : closedPoints MP.C := MP.placeEquiv.symm V.val
    let y : CE := I.inv x.val
    have hxy : I.hom y = x.val := by
      exact congrArg (fun a : MP.C ⟶ MP.C => a x.val) I.inv_hom_id
    have hy : y ∉ UE := by
      intro hy
      exact V.property ⟨⟨y, hy⟩, hxy⟩
    obtain ⟨z, hz⟩ := r.surjective y
    have hzout : z ∉ UΩ := by
      intro hzmem
      apply hy
      change pullback.fst c (specMap k E) y ∈ U
      have hproj : pullback.fst c (specMap k E) y = p₀ z := by
        rw [← hz]
        exact congrArg (fun a : M.C ⟶ C => a z) hr
      rw [hproj]
      exact hzmem
    have hη : genericPoint M.C ∈ UΩ :=
      ((genericPoint_spec M.C).mem_open_set_iff UΩ.isOpen).mpr
        ⟨(Classical.choice nonemptyUΩ).val, Set.mem_univ _,
          (Classical.choice nonemptyUΩ).property⟩
    have hzclosed : IsClosed ({z} : Set M.C) :=
      AlgebraicCurve.isClosed_singleton_of_ne_genericPoint M.toBase z
        (by rintro rfl; exact hzout hη)
    let b : B := ⟨M.placeOfPoint ⟨z, hzclosed⟩, by
      change (M.placeEquiv.symm (M.placeOfPoint ⟨z, hzclosed⟩)).val ∉ Set.range UΩ.ι
      rw [← M.placeEquiv_apply, M.placeEquiv.symm_apply_apply]
      rintro ⟨w, hw⟩
      have hw' : w.val = z := hw
      exact hzout (hw' ▸ w.property)⟩
    have hb : (M.placeEquiv.symm b.val).val = z := by
      change (M.placeEquiv.symm (M.placeOfPoint ⟨z, hzclosed⟩)).val = z
      rw [← M.placeEquiv_apply, M.placeEquiv.symm_apply_apply]
    have hyq : y = q b (IsLocalRing.closedPoint E) := by
      have h := hcenterE b
      rw [hb] at h
      exact hz.symm.trans h
    have hsection : (q b ≫ I.hom) ≫ MP.toBase = 𝟙 _ := by
      rw [Category.assoc, hI, hq b]
    have hxq : x.val = (q b ≫ I.hom) (IsLocalRing.closedPoint E) :=
      hxy.symm.trans (congrArg I.hom hyq)
    have hV : MP.placeOfPoint x = V.val := MP.placeEquiv.apply_symm_apply V.val
    rw [← hV]
    exact MP.isRational_placeOfPoint_of_section (q b ≫ I.hom) hsection x hxq
  obtain ⟨s, hs, J, hJ⟩ := exists_rationalConfiguration_iso_of_rationalBoundary E j hboundary
  refine ⟨E, hDE, I, hI, s, hs, J, hJ, ?_⟩
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ π E 1) hJ).trans
      ((Category.assoc UE.ι I.hom (π E 1)).trans
        (congrArg (UE.ι ≫ ·) hI)))

/-- A finite split open model without a prescribed lower constant field. -/
theorem exists_finiteGalois_rationalConfiguration_model
    {k Ω F : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    [IsAlgClosed Ω] [Field F] [Algebra Ω F] [Algebra k F] [IsScalarTower k Ω F]
    [IsCurveOver Ω F] [Algebra.EssFiniteType Ω F]
    (M : CurveModel Ω F) {C : Scheme} [IsIntegral C]
    (c : C ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    [GeometricallyIntegral c]
    (e : M.C ≅ pullback c (specMap k Ω))
    (he : e.hom ≫ pullback.snd c (specMap k Ω) = M.toBase)
    (hg : genusFF Ω F = 0) (U : C.Opens) (hU : (U : Set C).Nonempty) :
    ∃ E : FiniteGaloisIntermediateField k Ω,
      ∃ I : pullback c (specMap k E) ≅ (projectiveLineRatFuncModel E).C,
        I.hom ≫ (projectiveLineRatFuncModel E).toBase =
          pullback.snd c (specMap k E) ∧
        ∃ s : Finset (Projectivization E (E × E)),
          (∀ a, a ∈ s ↔ projectiveRationalPoint a ∉
            Set.range ((pullback.fst c (specMap k E) ⁻¹ᵁ U).ι ≫ I.hom)) ∧
          ∃ J : ((pullback.fst c (specMap k E) ⁻¹ᵁ U) : Scheme) ≅
              (rationalConfigurationOpen s : Scheme),
            J.hom ≫ (rationalConfigurationOpen s).ι =
              (pullback.fst c (specMap k E) ⁻¹ᵁ U).ι ≫ I.hom ∧
            J.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
              (pullback.fst c (specMap k E) ⁻¹ᵁ U).ι ≫
                pullback.snd c (specMap k E) := by
  obtain ⟨E, _hbot, hE⟩ := exists_finiteGalois_rationalConfiguration_model_above
    M c e he hg U hU ⊥
  exact ⟨E, hE⟩

end AnabelianGeometry.GeometricFundamentalGroup
