/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawPullbackCompEqMulEq

/-!
# Factoring through the canonical base-changed group model

Retaining the explicit base-changed group law also retains its commutativity.
The generic comparison preserves the original group operation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq.DescB

namespace GoodReductionJacobian.RelativeGroupLaw

/-- Factor an actual generic group-model comparison through a coefficient
ring map, keeping the canonical base-changed group law in the conclusion. -/
theorem exists_baseChange_model_map
    {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂]
    {A : Scheme} {f : A ⟶ Spec (.of R)} (G : RelativeGroupLaw R f)
    (φ₁ : R₁ →+* R) (φ₂ : R₂ →+* R) (ψ : R₁ →+* R₂)
    (hψ : φ₂.comp ψ = φ₁)
    {A₁ : Scheme} {f₁ : A₁ ⟶ Spec (.of R₁)} (G₁ : RelativeGroupLaw R₁ f₁)
    (a₁ : A ⟶ A₁) (ha₁ : IsPullback a₁ f f₁ (Spec.map (CommRingCat.ofHom φ₁)))
    (hmul : ∀ (T : Scheme) (t : T ⟶ Spec (.of R)) (P Q : SchemeHomOver t f),
      (G.mul t P Q).1 ≫ a₁ =
        (G₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ₁))
          ⟨P.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, Q.2]⟩).1) :
    let ι := Spec.map (CommRingCat.ofHom ψ)
    ∃ a₂ : A ⟶ pullback f₁ ι,
      ∃ ha₂ : IsPullback a₂ f (pullback.snd f₁ ι) (Spec.map (CommRingCat.ofHom φ₂)),
        a₂ ≫ pullback.fst f₁ ι = a₁ ∧
        ∀ (T : Scheme) (t : T ⟶ Spec (.of R)) (P Q : SchemeHomOver t f),
          (G.mul t P Q).1 ≫ a₂ =
            ((G₁.baseChange ι).mul (t ≫ Spec.map (CommRingCat.ofHom φ₂))
              ⟨P.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, Q.2]⟩).1 := by
  intro ι
  have hSpec : Spec.map (CommRingCat.ofHom φ₁) =
      Spec.map (CommRingCat.ofHom φ₂) ≫ ι := by
    rw [← hψ, CommRingCat.ofHom_comp, Spec.map_comp]
  let a₂ : A ⟶ pullback f₁ ι :=
    pullback.lift a₁ (f ≫ Spec.map (CommRingCat.ofHom φ₂))
      (by rw [ha₁.w, hSpec, Category.assoc])
  have hfst : a₂ ≫ pullback.fst f₁ ι = a₁ := pullback.lift_fst _ _ _
  have hsnd : a₂ ≫ pullback.snd f₁ ι = f ≫ Spec.map (CommRingCat.ofHom φ₂) :=
    pullback.lift_snd _ _ _
  have ha₂ : IsPullback a₂ f (pullback.snd f₁ ι) (Spec.map (CommRingCat.ofHom φ₂)) := by
    refine IsPullback.of_right ?_ hsnd (IsPullback.of_hasPullback f₁ ι)
    rw [hfst, ← hSpec]
    exact ha₁
  refine ⟨a₂, ha₂, hfst, ?_⟩
  intro T t P Q
  apply pullback.hom_ext
  · rw [Category.assoc, hfst, hmul T t P Q, baseChange_mul_fst]
    exact mul_val_congr G₁ (by rw [hSpec, Category.assoc]) _ _ _ _
      (show P.1 ≫ a₁ = (P.1 ≫ a₂) ≫ pullback.fst f₁ ι by
        rw [Category.assoc, hfst])
      (show Q.1 ≫ a₁ = (Q.1 ≫ a₂) ≫ pullback.fst f₁ ι by
        rw [Category.assoc, hfst])
  · have h : (G.mul t P Q).1 ≫ a₂ ≫ pullback.snd f₁ ι =
        t ≫ Spec.map (CommRingCat.ofHom φ₂) := by
      rw [hsnd, ← Category.assoc, (G.mul t P Q).2]
    rw [Category.assoc]
    exact h.trans (((G₁.baseChange ι).mul (t ≫ Spec.map (CommRingCat.ofHom φ₂))
      ⟨P.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, Q.2]⟩).2).symm

end GoodReductionJacobian.RelativeGroupLaw
