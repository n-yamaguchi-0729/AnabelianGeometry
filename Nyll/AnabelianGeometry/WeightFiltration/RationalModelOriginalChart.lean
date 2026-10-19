/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.FiniteRationalModelBaseChange
import Nyll.AnabelianGeometry.ProjectiveLine.ConfigurationScalarExtension
import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.OpenBaseChange

/-! # The original proper chart of the specified finite rational model

The open chart is exactly the scalar extension used by the pointed-group
comparison. Its proper model is supplied by the same finite proper model.
The projection and coefficient equations follow from the actual ambient
square, with no extra model-compatibility condition.
-/

noncomputable section
open AlgebraicGeometry.SmoothProperCurve
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace
open AnabelianGeometry.GeometricFundamentalGroup
open AnabelianGeometry.ArithmeticIsomorphisms AnabelianGeometry.ProjectiveLine

namespace AnabelianGeometry.WeightFiltration

/-- The very same scalar-extended open model supplies a proper projective-line
chart of the original geometric curve, including both structural equations
required by its Galois action on boundary places. -/
theorem exists_original_rationalModel_chart
    (k E κ : Type) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    {C : Scheme} (c : C ⟶ Spec (.of k)) (U : C.Opens)
    (I : pullback c (specMap k E) ≅ (projectiveLineRatFuncModel E).C)
    (hI : I.hom ≫ (projectiveLineRatFuncModel E).toBase =
      pullback.snd c (specMap k E))
    (s : Finset (Projectivization E (E × E)))
    (J : pullback (specMap k E) (U.ι ≫ c) ≅ (rationalConfigurationOpen s : Scheme))
    (hJ : J.hom ≫ (rationalConfigurationOpen s).ι =
      (openBaseChangeIso c (specMap k E) U).hom ≫
        (pullback.fst c (specMap k E) ⁻¹ᵁ U).ι ≫ I.hom)
    (hJbase : J.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
      pullback.fst (specMap k E) (U.ι ≫ c)) :
    let B := scalarExtensionModelIso k E κ (U.ι ≫ c)
      ((rationalConfigurationOpen s).ι ≫ π E 1) J hJbase
    let j := B.hom ≫ rationalConfigurationBaseChangeChart E κ s
    ∃ eC : (projectiveLineRatFuncModel κ).C ≅ pullback c (specMap k κ),
      eC.hom ≫ pullback.snd c (specMap k κ) = (projectiveLineRatFuncModel κ).toBase ∧
      j ≫ eC.hom ≫ pullback.fst c (specMap k κ) =
        pullback.snd (specMap k κ) (U.ι ≫ c) ≫ U.ι ∧
      j ≫ (projectiveLineRatFuncModel κ).toBase =
        pullback.fst (specMap k κ) (U.ι ≫ c) := by
  intro B j
  let BE := openBaseChangeIso c (specMap k E) U
  let JN := BE.symm ≪≫ J
  let Ihom : pullback c (specMap k E) ⟶ projectiveLineScheme E := I.hom
  have hJambient : J.hom ≫ (rationalConfigurationOpen s).ι =
      BE.hom ≫ (pullback.fst c (specMap k E) ⁻¹ᵁ U).ι ≫ Ihom := hJ
  have hJN : JN.hom ≫ (rationalConfigurationOpen s).ι =
      (pullback.fst c (specMap k E) ⁻¹ᵁ U).ι ≫ I.hom := by
    change (BE.inv ≫ J.hom) ≫ _ = _
    change (BE.inv ≫ J.hom) ≫ (rationalConfigurationOpen s).ι =
      (pullback.fst c (specMap k E) ⁻¹ᵁ U).ι ≫ Ihom
    exact (Category.assoc _ _ _).trans
      ((congrArg (BE.inv ≫ ·) hJambient).trans (BE.inv_hom_id_assoc _))
  obtain ⟨IL, hIL, JL, _hJLbase, hJLambient, hJLmodel⟩ :=
    exists_rationalModelScalarExtension_with_ambient k E κ c U I hI s JN hJN
  have hJback : BE ≪≫ JN = J := by
    apply Iso.ext
    change BE.hom ≫ (BE.inv ≫ J.hom) = J.hom
    exact BE.hom_inv_id_assoc J.hom
  have hJL : JL = rationalModelScalarExtensionIso k E κ (U.ι ≫ c) s J hJbase := by
    change JL = rationalModelScalarExtensionIso k E κ (U.ι ≫ c) s (BE ≪≫ JN) _
      at hJLmodel
    simpa only [hJback] using hJLmodel
  let Iκ : pullback c (specMap k κ) ≅ projectiveLineScheme κ := IL
  have hambient : j = (openBaseChangeIso c (specMap k κ) U).hom ≫
      (pullback.fst c (specMap k κ) ⁻¹ᵁ U).ι ≫ Iκ.hom := by
    rw [hJL] at hJLambient
    change (B.hom ≫ (rationalConfigurationScalarExtensionIso E κ s).hom) ≫
      (rationalConfigurationOpen (configurationScalarExtension E κ s)).ι = _ at hJLambient
    rw [Category.assoc, rationalConfigurationScalarExtensionIso_hom_chart] at hJLambient
    exact hJLambient
  refine ⟨IL.symm, ?_, ?_, ?_⟩
  · exact (congrArg (IL.inv ≫ ·) hIL).symm.trans (IL.inv_hom_id_assoc _)
  · change j ≫ Iκ.inv ≫ pullback.fst c (specMap k κ) = _
    rw [hambient]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact openBaseChangeIso_hom_comp_ambient c (specMap k κ) U
  · change (B.hom ≫ rationalConfigurationBaseChangeChart E κ s) ≫ π κ 1 = _
    rw [Category.assoc, rationalConfigurationBaseChangeChart_comp_π]
    exact scalarExtensionModelIso_hom_comp_base k E κ (U.ι ≫ c)
      ((rationalConfigurationOpen s).ι ≫ π E 1) J hJbase

end AnabelianGeometry.WeightFiltration
