/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.FiniteRationalModelBaseChange
import Nyll.AnabelianGeometry.WeightFiltration.FiniteRationalModelBoundaryCard

/-! # Two genus-zero opens over one finite Galois field

Both rational models and both puncture-cardinality bounds are constructed.
The first model is extended to the splitting field of the second, so the
output uses one actual finite constant extension rather than two unrelated
fields or an assumed simultaneous splitting datum.
-/

noncomputable section

open AlgebraicGeometry.SmoothProperCurve
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace AnabelianGeometry.ArithmeticIsomorphisms
open AnabelianGeometry.ProjectiveLine AnabelianGeometry.WeightFiltration

namespace AnabelianGeometry.GeometricFundamentalGroup

/-- Two geometrically genus-zero opens with at least three geometric punctures
have actual rational-configuration models over a common finite Galois field.
The maps are isomorphisms of the native constant-cover schemes over that field. -/
theorem exists_common_finiteGalois_rationalConfiguration_models
    {k κ F₁ F₂ : Type} [Field k] [Field κ] [Algebra k κ] [IsGalois k κ]
    [IsAlgClosed κ] [Field F₁] [Field F₂]
    [Algebra κ F₁] [Algebra k F₁] [IsScalarTower k κ F₁]
    [Algebra κ F₂] [Algebra k F₂] [IsScalarTower k κ F₂]
    [IsCurveOver κ F₁] [Algebra.EssFiniteType κ F₁]
    [IsCurveOver κ F₂] [Algebra.EssFiniteType κ F₂]
    (M₁ : CurveModel κ F₁) (M₂ : CurveModel κ F₂)
    {C₁ C₂ : Scheme} [IsIntegral C₁] [IsIntegral C₂]
    (c₁ : C₁ ⟶ Spec (.of k)) (c₂ : C₂ ⟶ Spec (.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (e₁ : M₁.C ≅ pullback c₁ (specMap k κ))
    (e₂ : M₂.C ≅ pullback c₂ (specMap k κ))
    (he₁ : e₁.hom ≫ pullback.snd c₁ (specMap k κ) = M₁.toBase)
    (he₂ : e₂.hom ≫ pullback.snd c₂ (specMap k κ) = M₂.toBase)
    (hg₁ : genusFF κ F₁ = 0) (hg₂ : genusFF κ F₂ = 0)
    (U₁ : C₁.Opens) (U₂ : C₂.Opens)
    (hU₁ : (U₁ : Set C₁).Nonempty) (hU₂ : (U₂ : Set C₂).Nonempty)
    (hr₁ : 3 ≤ Nat.card (M₁.openBoundaryPlaces
      (((e₁.hom ≫ pullback.fst c₁ (specMap k κ)) ⁻¹ᵁ U₁).ι)))
    (hr₂ : 3 ≤ Nat.card (M₂.openBoundaryPlaces
      (((e₂.hom ≫ pullback.fst c₂ (specMap k κ)) ⁻¹ᵁ U₂).ι))) :
    ∃ E : FiniteGaloisIntermediateField k κ,
      ∃ s t : Finset (Projectivization E (E × E)),
        3 ≤ s.card ∧ 3 ≤ t.card ∧
        ∃ (I₁ : pullback c₁ (specMap k E) ≅ (projectiveLineRatFuncModel E).C)
          (I₂ : pullback c₂ (specMap k E) ≅ (projectiveLineRatFuncModel E).C),
          I₁.hom ≫ (projectiveLineRatFuncModel E).toBase =
            pullback.snd c₁ (specMap k E) ∧
          I₂.hom ≫ (projectiveLineRatFuncModel E).toBase =
            pullback.snd c₂ (specMap k E) ∧
        ∃ (Js : pullback (specMap k E) (U₁.ι ≫ c₁) ≅
            (rationalConfigurationOpen s : Scheme))
          (Jt : pullback (specMap k E) (U₂.ι ≫ c₂) ≅
            (rationalConfigurationOpen t : Scheme)),
          Js.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
            pullback.fst (specMap k E) (U₁.ι ≫ c₁) ∧
          Jt.hom ≫ ((rationalConfigurationOpen t).ι ≫ π E 1) =
            pullback.fst (specMap k E) (U₂.ι ≫ c₂) ∧
          Js.hom ≫ (rationalConfigurationOpen s).ι =
            (openBaseChangeIso c₁ (specMap k E) U₁).hom ≫
              (pullback.fst c₁ (specMap k E) ⁻¹ᵁ U₁).ι ≫ I₁.hom ∧
          Jt.hom ≫ (rationalConfigurationOpen t).ι =
            (openBaseChangeIso c₂ (specMap k E) U₂).hom ≫
              (pullback.fst c₂ (specMap k E) ⁻¹ᵁ U₂).ι ≫ I₂.hom := by
  obtain ⟨E₀, _hbot, I₀, hI₀, s₀, _hs₀, J₀, hJ₀, _hJ₀base⟩ :=
    exists_finiteGalois_rationalConfiguration_model_above
      M₁ c₁ e₁ he₁ hg₁ U₁ hU₁ ⊥
  have hcard₀ := finiteRationalModel_card_eq_original_boundary_card
    k E₀ κ M₁ c₁ e₁ he₁ U₁ I₀ hI₀ s₀ J₀ hJ₀
  have hs₀ : 3 ≤ s₀.card := by
    rw [hcard₀]
    exact hr₁
  obtain ⟨E, hE, I₂, hI₂, t, _ht, J₂, hJ₂, hJ₂base⟩ :=
    exists_finiteGalois_rationalConfiguration_model_above
      M₂ c₂ e₂ he₂ hg₂ U₂ hU₂ E₀
  have hcard₂ := finiteRationalModel_card_eq_original_boundary_card
    k E κ M₂ c₂ e₂ he₂ U₂ I₂ hI₂ t J₂ hJ₂
  have ht : 3 ≤ t.card := by
    rw [hcard₂]
    exact hr₂
  let ι : E₀ →ₐ[k] E := IntermediateField.inclusion
    ((FiniteGaloisIntermediateField.le_iff E₀ E).mp hE)
  let : Algebra E₀ E := ι.toRingHom.toAlgebra
  have : IsScalarTower k E₀ E :=
    IsScalarTower.of_algebraMap_eq (fun a => (ι.commutes a).symm)
  let s := configurationScalarExtension E₀ E s₀
  obtain ⟨I₁, hI₁, Js, hJs, hJsambient, _hJsmodel⟩ :=
    exists_rationalModelScalarExtension_with_ambient k E₀ E c₁ U₁ I₀ hI₀ s₀ J₀ hJ₀
  let B₂ := openBaseChangeIso c₂ (specMap k E) U₂
  let Jt := B₂ ≪≫ J₂
  have hs : 3 ≤ s.card := by
    rw [configurationScalarExtension_card]
    exact hs₀
  refine ⟨E, s, t, hs, ht, I₁, I₂, hI₁, hI₂, Js, Jt, hJs, ?_, hJsambient, ?_⟩
  · change (B₂.hom ≫ J₂.hom) ≫ _ = _
    rw [Category.assoc, hJ₂base]
    exact openBaseChangeIso_hom_comp_base c₂ (specMap k E) U₂
  · change (B₂.hom ≫ J₂.hom) ≫ _ = _
    rw [Category.assoc, hJ₂]
    rfl

end AnabelianGeometry.GeometricFundamentalGroup
