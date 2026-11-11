/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupTwoStepExtension
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Actual pushout representatives of connecting classes

Pushing a short exact sequence out along a coefficient morphism gives
an actual short exact sequence. Its original Ext class is the original
connecting class, and its canonical middle lift has exactly the given
coefficient morphism as its kernel difference. In particular this
constructs module extensions from actual Cech cocycles; an extension
or a compatibility with its local differences need not be assumed.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory Limits Abelian

namespace EtaleCohomology.CupPushoutExtension

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The original quotient morphism descends across the actual pushout. -/
def projection (S : ShortComplex C) {F : C} (k : S.X₁ ⟶ F) :
    pushout S.f k ⟶ S.X₃ :=
  pushout.desc S.g 0 (by rw [S.zero, comp_zero])

theorem inl_projection (S : ShortComplex C) {F : C} (k : S.X₁ ⟶ F) :
    pushout.inl S.f k ≫ projection S k = S.g :=
  pushout.inl_desc S.g 0 _

theorem inr_projection (S : ShortComplex C) {F : C} (k : S.X₁ ⟶ F) :
    pushout.inr S.f k ≫ projection S k = 0 :=
  pushout.inr_desc S.g 0 _

/-- The original coefficient object is the actual kernel of the
pushout quotient. -/
def sequence (S : ShortComplex C) {F : C} (k : S.X₁ ⟶ F) : ShortComplex C :=
  ShortComplex.mk (pushout.inr S.f k) (projection S k) (inr_projection S k)

/-- Exactness follows from the original cokernel universal property
and the actual pushout universal property. -/
theorem shortExact (S : ShortComplex C) (hS : S.ShortExact)
    {F : C} (k : S.X₁ ⟶ F) : (sequence S k).ShortExact := by
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  have hmono : Mono (pushout.inr S.f k) := Abelian.mono_pushout_of_mono_f S.f k
  have hepi : Epi (projection S k) := epi_of_epi_fac (inl_projection S k)
  refine { exact := ?_, mono_f := hmono, epi_g := hepi }
  apply (sequence S k).exact_of_g_is_cokernel
  refine CokernelCofork.IsColimit.ofπ' (projection S k) (inr_projection S k) ?_
  intro W t ht
  have hft : S.f ≫ (pushout.inl S.f k ≫ t) = 0 := by
    rw [← Category.assoc, pushout.condition, Category.assoc, ht, comp_zero]
  refine ⟨hS.exact.desc (pushout.inl S.f k ≫ t) hft, ?_⟩
  apply pushout.hom_ext
  · rw [← Category.assoc, inl_projection, hS.exact.g_desc]
  · rw [← Category.assoc, inr_projection, zero_comp, ht]

/-- The same actual pushout square is a morphism of short complexes. -/
def morphism (S : ShortComplex C) {F : C} (k : S.X₁ ⟶ F) :
    S ⟶ sequence S k where
  τ₁ := k
  τ₂ := pushout.inl S.f k
  τ₃ := 𝟙 S.X₃
  comm₁₂ := pushout.condition.symm
  comm₂₃ := (inl_projection S k).trans (Category.comp_id S.g).symm

/-- Its native extension class is the given connecting class. -/
theorem extClass [HasExt.{w} C] (S : ShortComplex C) (hS : S.ShortExact)
    {F : C} (k : S.X₁ ⟶ F) :
    (shortExact S hS k).extClass =
      hS.extClass.comp (Ext.mk₀ k) (add_zero 1) := by
  have hn := hS.extClass_naturality (shortExact S hS k) (morphism S k)
  change hS.extClass.comp (Ext.mk₀ k) (add_zero 1) =
    (Ext.mk₀ (𝟙 S.X₃)).comp (shortExact S hS k).extClass (zero_add 1) at hn
  exact (hn.trans (Ext.mk₀_id_comp (shortExact S hS k).extClass)).symm

/-- The canonical middle lift retains the exact original coefficient
morphism as its kernel difference. -/
theorem difference (S : ShortComplex C) (hS : S.ShortExact)
    {F : C} (k : S.X₁ ⟶ F) :
    CupTwoStepExtension.difference S (sequence S k) (shortExact S hS k)
      (𝟙 S.X₃) (pushout.inl S.f k)
      ((inl_projection S k).trans (Category.comp_id S.g).symm) = k := by
  have : Mono (sequence S k).f := (shortExact S hS k).mono_f
  apply (cancel_mono (sequence S k).f).mp
  exact (CupTwoStepExtension.difference_comp S (sequence S k) (shortExact S hS k)
    (𝟙 S.X₃) (pushout.inl S.f k)
    ((inl_projection S k).trans (Category.comp_id S.g).symm)).trans pushout.condition

end EtaleCohomology.CupPushoutExtension
