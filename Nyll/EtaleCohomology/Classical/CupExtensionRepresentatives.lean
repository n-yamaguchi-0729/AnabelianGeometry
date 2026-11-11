/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantCoefficientUnit
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Actual short extensions representing original degree-one cohomology

Every degree-one class is represented by an actual short exact sequence
of the original module sheaves. The representative is constructed by
embedding its target in an actual injective, lifting the class through
the original Ext sequence, and taking the actual categorical pullback.
The resulting extension class is the given class under the existing
constant-source comparison. No extension representative or tensor
exactness is an extra hypothesis.
-/

@[expose] public section

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

section ShortExtensions

variable {C : Type u} [Category.{v} C] [Abelian C]

private def monoCokernelPullback {Y I X : C} (i : Y ⟶ I)
    (f : X ⟶ cokernel i) : ShortComplex C :=
  ShortComplex.mk
    (pullback.lift i (0 : Y ⟶ X) (by rw [cokernel.condition, zero_comp]))
    (pullback.snd (cokernel.π i) f)
    (pullback.lift_snd _ _ _)

private theorem monoCokernelPullback_shortExact
    {Y I X : C} (i : Y ⟶ I) [Mono i] (f : X ⟶ cokernel i) :
    (monoCokernelPullback i f).ShortExact := by
  let P := ShortComplex.mk
    (pullback.lift i (0 : Y ⟶ X) (by rw [cokernel.condition, zero_comp]))
    (pullback.snd (cokernel.π i) f) (pullback.lift_snd _ _ _)
  have hmono : Mono P.f := mono_of_mono_fac
    (show P.f ≫ pullback.fst (cokernel.π i) f = i from
      pullback.lift_fst _ _ _)
  have hkernel : IsLimit (KernelFork.ofι P.f P.zero) := by
    apply KernelFork.IsLimit.ofι'
    intro A k hk
    have hk' : (k ≫ pullback.fst (cokernel.π i) f) ≫ cokernel.π i = 0 := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      change (k ≫ P.g) ≫ f = 0
      rw [hk, zero_comp]
    refine ⟨Abelian.monoLift i (k ≫ pullback.fst (cokernel.π i) f) hk', ?_⟩
    apply pullback.hom_ext
    · change (Abelian.monoLift i _ hk' ≫ pullback.lift i (0 : Y ⟶ X) _) ≫
        pullback.fst (cokernel.π i) f = k ≫ pullback.fst (cokernel.π i) f
      rw [Category.assoc, pullback.lift_fst, Abelian.monoLift_comp]
    · change (Abelian.monoLift i _ hk' ≫ pullback.lift i (0 : Y ⟶ X) _) ≫
        pullback.snd (cokernel.π i) f = k ≫ P.g
      rw [Category.assoc, pullback.lift_snd, comp_zero]
      exact hk.symm
  exact
    { exact := P.exact_of_f_is_kernel hkernel
      mono_f := hmono
      epi_g := inferInstanceAs (Epi (pullback.snd (cokernel.π i) f)) }

/-- Every degree-one Ext class in an abelian category with enough
injectives is represented by an actual short exact sequence. The source
is arbitrary, so the same construction also applies to covering objects. -/
theorem ext_one_exists_shortExact
    [HasExt.{w} C] [EnoughInjectives C] {X Y : C} (a : Ext.{w} X Y 1) :
    ∃ (E : C) (i : Y ⟶ E) (p : E ⟶ X) (h : i ≫ p = 0)
      (hS : (ShortComplex.mk i p h).ShortExact), hS.extClass = a := by
  let S := ShortComplex.mk (Injective.ι Y) (cokernel.π (Injective.ι Y))
    (cokernel.condition (Injective.ι Y))
  have hS : S.ShortExact :=
    { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel (Injective.ι Y)) }
  obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁ X hS a
    (Ext.eq_zero_of_injective _) (n₀ := 0) rfl
  let f : X ⟶ cokernel (Injective.ι Y) := Ext.homEquiv₀ b
  let P := ShortComplex.mk
    (pullback.lift (Injective.ι Y) (0 : Y ⟶ X)
      (by rw [cokernel.condition, zero_comp]))
    (pullback.snd (cokernel.π (Injective.ι Y)) f) (pullback.lift_snd _ _ _)
  have hP : P.ShortExact := monoCokernelPullback_shortExact (Injective.ι Y) f
  let φ : P ⟶ S :=
    { τ₁ := 𝟙 Y
      τ₂ := pullback.fst (cokernel.π (Injective.ι Y)) f
      τ₃ := f
      comm₁₂ := by
        change 𝟙 Y ≫ Injective.ι Y =
          pullback.lift (Injective.ι Y) (0 : Y ⟶ X) _ ≫
            pullback.fst (cokernel.π (Injective.ι Y)) f
        rw [Category.id_comp, pullback.lift_fst]
      comm₂₃ := pullback.condition }
  have hclass : hP.extClass = (Ext.mk₀ f).comp hS.extClass (zero_add 1) := by
    have hn := hP.extClass_naturality hS φ
    change hP.extClass.comp (Ext.mk₀ (𝟙 Y)) (add_zero 1) =
      (Ext.mk₀ f).comp hS.extClass (zero_add 1) at hn
    exact (Ext.comp_mk₀_id hP.extClass).symm.trans hn
  refine ⟨P.X₂, P.f, P.g, P.zero, hP, ?_⟩
  calc
    hP.extClass = (Ext.mk₀ f).comp hS.extClass (zero_add 1) := hclass
    _ = b.comp hS.extClass (zero_add 1) := by
      rw [show Ext.mk₀ f = b from Ext.mk₀_homEquiv₀_apply b]
    _ = a := hb

end ShortExtensions

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- Every original module Ext class in degree one is the extension
class of an actual short exact sequence in the same module-sheaf category. -/
theorem etaleModuleExt_one_exists_shortExact
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (a : Ext.{u} F G 1) :
    ∃ (E : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
      (i : G ⟶ E) (p : E ⟶ F) (h : i ≫ p = 0)
      (hS : (ShortComplex.mk i p h).ShortExact), hS.extClass = a :=
  ext_one_exists_shortExact a

/-- Every actual degree-one cohomology class is represented by an
actual extension of the original constant regular coefficient sheaf. -/
theorem etaleCohomologyH1_exists_shortExact
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (a : etaleCohomology X R F 1) :
    ∃ (E : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
      (i : F ⟶ E)
      (p : E ⟶ (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)) (h : i ≫ p = 0)
      (hS : (ShortComplex.mk i p h).ShortExact),
      etaleConstantModuleExtCohomologyEquiv X R F 1 hS.extClass = a := by
  let e := etaleConstantModuleExtCohomologyEquiv X R F 1
  obtain ⟨E, i, p, h, hS, he⟩ :=
    etaleModuleExt_one_exists_shortExact X R (e.symm a)
  exact ⟨E, i, p, h, hS, (congrArg e he).trans (e.apply_symm_apply a)⟩

/-- The original coefficient inclusion of the representing extension
kills its own original degree-one cohomology class. -/
theorem etaleCohomologyH1_extension_coefficientMap_eq_zero
    {F E : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (i : F ⟶ E)
    (p : E ⟶ (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)) (h : i ≫ p = 0)
    (hS : (ShortComplex.mk i p h).ShortExact) :
    Classical.cohomologyMap i 1
      (etaleConstantModuleExtCohomologyEquiv X R F 1 hS.extClass) = 0 := by
  rw [← etaleConstantModuleExtCohomologyEquiv_naturality,
    hS.extClass_comp, map_zero]
  rfl

end EtaleCohomology
