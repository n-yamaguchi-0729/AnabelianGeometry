/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Restricting an actual extension to a kernel

Let `A → B → C` be short exact and let `h : B → D` restrict to an
epimorphism `t : A → D`. Then the original kernels give the short exact
sequence `ker t → ker h → C`. The construction keeps both original
kernel inclusions and computes the induced original extension class.
-/

@[expose] public section

noncomputable section

universe w v u

open CategoryTheory Limits

namespace EtaleFundamentalGroups.Cohomology

variable {C : Type u} [Category.{v} C] [Abelian C]
  (S : ShortComplex C) {D : C} (t : S.X₁ ⟶ D) (h : S.X₂ ⟶ D)
  (w : S.f ≫ h = t)

/-- Restrict the original extension to the kernel of its specified
middle-term map, retaining the original kernel of the restriction. -/
def kernelRestrictionExtension : ShortComplex C :=
  ShortComplex.mk
    (kernel.lift h (kernel.ι t ≫ S.f) (by
      rw [Category.assoc, w, kernel.condition]))
    (kernel.ι h ≫ S.g)
    (by rw [← Category.assoc, kernel.lift_ι, Category.assoc,
      S.zero, comp_zero])

/-- The kernel inclusion of the restricted extension is the original
kernel inclusion followed by the original extension inclusion. -/
theorem kernelRestrictionExtension_f_ι :
    (kernelRestrictionExtension S t h w).f ≫ kernel.ι h =
      kernel.ι t ≫ S.f :=
  kernel.lift_ι _ _ _

/-- Taking this kernel preserves exactness at the middle term. -/
theorem kernelRestrictionExtension_exact (hS : S.ShortExact) :
    (kernelRestrictionExtension S t h w).Exact := by
  let K := kernelRestrictionExtension S t h w
  have : Mono S.f := hS.mono_f
  have : Mono K.f := by
    dsimp only [K, kernelRestrictionExtension]
    infer_instance
  apply K.exact_of_f_is_kernel
  apply KernelFork.IsLimit.ofι'
  intro T k hk
  change T ⟶ kernel h at k
  change k ≫ (kernel.ι h ≫ S.g) = 0 at hk
  have hk' : (k ≫ kernel.ι h) ≫ S.g = 0 := by
    simpa only [Category.assoc] using hk
  let a : T ⟶ S.X₁ := hS.exact.lift (k ≫ kernel.ι h) hk'
  have ha : a ≫ S.f = k ≫ kernel.ι h := hS.exact.lift_f _ _
  have hat : a ≫ t = 0 := by
    rw [← w, ← Category.assoc, ha, Category.assoc,
      kernel.condition, comp_zero]
  change { l : T ⟶ kernel t //
    l ≫ (kernelRestrictionExtension S t h w).f = k }
  refine ⟨kernel.lift t a hat, ?_⟩
  apply (cancel_mono (kernel.ι h)).mp
  change (kernel.lift t a hat ≫
    kernel.lift h (kernel.ι t ≫ S.f)
      (by rw [Category.assoc, w, kernel.condition])) ≫ kernel.ι h =
    k ≫ kernel.ι h
  rw [Category.assoc, kernel.lift_ι,
    ← Category.assoc, kernel.lift_ι, ha]

/-- The original quotient map remains epimorphic because the
restriction `t` is an epimorphism. -/
theorem kernelRestrictionExtension_epi [Epi t] (hS : S.ShortExact) :
    Epi (kernelRestrictionExtension S t h w).g := by
  change Epi (kernel.ι h ≫ S.g)
  have : Epi S.g := hS.epi_g
  have : Epi h := epi_of_epi_fac w
  apply Abelian.epi_of_cokernel_π_eq_zero
  have hz : kernel.ι h ≫ (S.g ≫ cokernel.π (kernel.ι h ≫ S.g)) = 0 := by
    rw [← Category.assoc, cokernel.condition]
  let v : D ⟶ cokernel (kernel.ι h ≫ S.g) :=
    Abelian.epiDesc h (S.g ≫ cokernel.π (kernel.ι h ≫ S.g)) hz
  have hv : h ≫ v = S.g ≫ cokernel.π (kernel.ι h ≫ S.g) :=
    Abelian.comp_epiDesc h _ hz
  have htv : t ≫ v = 0 := by
    rw [← w, Category.assoc, hv, ← Category.assoc,
      S.zero, zero_comp]
  have hv0 : v = 0 := (cancel_epi t).mp (htv.trans (comp_zero).symm)
  have hgπ : S.g ≫ cokernel.π (kernel.ι h ≫ S.g) = 0 := by
    rw [← hv, hv0, comp_zero]
  exact (cancel_epi S.g).mp (hgπ.trans (comp_zero).symm)

/-- The actual kernels form a short exact sequence, without a
chosen lift or a supplied exactness comparison. -/
theorem kernelRestrictionExtension_shortExact [Epi t] (hS : S.ShortExact) :
    (kernelRestrictionExtension S t h w).ShortExact := by
  have : Mono S.f := hS.mono_f
  have : Mono (kernelRestrictionExtension S t h w).f := by
    dsimp only [kernelRestrictionExtension]
    infer_instance
  have : Epi (kernelRestrictionExtension S t h w).g :=
    kernelRestrictionExtension_epi S t h w hS
  exact { exact := kernelRestrictionExtension_exact S t h w hS }

/-- The actual kernel inclusions give the original morphism of
extensions, with the identity on the quotient. -/
def kernelRestrictionExtensionToOriginal :
    kernelRestrictionExtension S t h w ⟶ S where
  τ₁ := kernel.ι t
  τ₂ := kernel.ι h
  τ₃ := 𝟙 S.X₃
  comm₁₂ := (kernelRestrictionExtension_f_ι S t h w).symm
  comm₂₃ := (Category.comp_id _).symm

/-- The restricted extension maps to the original Ext class through
the original kernel inclusion. -/
theorem kernelRestrictionExtension_extClass [HasExt.{w} C] [Epi t]
    (hS : S.ShortExact) :
    (kernelRestrictionExtension_shortExact S t h w hS).extClass.comp
        (Abelian.Ext.mk₀ (kernel.ι t)) (add_zero 1) = hS.extClass := by
  have hn := ShortComplex.ShortExact.extClass_naturality
    (kernelRestrictionExtension_shortExact S t h w hS) hS
    (kernelRestrictionExtensionToOriginal S t h w)
  change (kernelRestrictionExtension_shortExact S t h w hS).extClass.comp
      (Abelian.Ext.mk₀ (kernel.ι t)) (add_zero 1) =
    (Abelian.Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (zero_add 1) at hn
  exact hn.trans (Abelian.Ext.mk₀_id_comp hS.extClass)

end EtaleFundamentalGroups.Cohomology
