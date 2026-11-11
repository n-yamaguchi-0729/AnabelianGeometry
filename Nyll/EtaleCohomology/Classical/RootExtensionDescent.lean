/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupExtensionInterchange
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionPullback
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionPullbackClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-!
# Descent retaining a specified root extension

An actual coefficient-root extension over a covering source and the
original extension are compared over the original augmentation. Their
proved equality of extension classes supplies an actual middle map.
Its kernel row is an actual extension, by the snake lemma.

The resulting three-by-three diagram retains both the specified root
extension and its original coefficient inclusion. The existing extension
interchange theorem computes its transgression, including the sign.
No middle map, kernel-row exactness, or transgression equality is assumed.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory Limits Abelian
open EtaleFundamentalGroups.Cohomology

namespace EtaleCohomology

/-- A specified root extension constructs an actual descent extension.
Its coefficient image is the restriction of that same root extension,
and its transgression is the negative of the original coefficient
boundary. Both identities follow from the constructed exact diagram. -/
theorem exists_rootExtension_descent
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    (S A : ShortComplex C) (hS : S.ShortExact) (hA : A.ShortExact)
    {Eβ Eα : C}
    (iβ : S.X₂ ⟶ Eβ) (pβ : Eβ ⟶ A.X₂) (zβ : iβ ≫ pβ = 0)
    (hβ : (ShortComplex.mk iβ pβ zβ).ShortExact)
    (iα : S.X₃ ⟶ Eα) (pα : Eα ⟶ A.X₃) (zα : iα ≫ pα = 0)
    (hα : (ShortComplex.mk iα pα zα).ShortExact)
    (hroot : hβ.extClass.comp (Ext.mk₀ S.g) (add_zero 1) =
      (Ext.mk₀ A.g).comp hα.extClass (zero_add 1)) :
    ∃ (E : C) (i : S.X₁ ⟶ E) (p : E ⟶ A.X₁) (z : i ≫ p = 0)
      (hE : (ShortComplex.mk i p z).ShortExact)
      (j : E ⟶ Eβ) (m : Eβ ⟶ Eα),
      iβ ≫ m = S.g ≫ iα ∧ m ≫ pα = pβ ≫ A.g ∧
      i ≫ j = S.f ≫ iβ ∧ j ≫ pβ = p ≫ A.f ∧ j ≫ m = 0 ∧
      hE.extClass.comp (Ext.mk₀ S.f) (add_zero 1) =
        (Ext.mk₀ A.f).comp hβ.extClass (zero_add 1) ∧
      hA.extClass.comp hE.extClass (show 1 + 1 = 2 from rfl) +
        hα.extClass.comp hS.extClass (show 1 + 1 = 2 from rfl) = 0 := by
  let B := ShortComplex.mk iβ pβ zβ
  let H := ShortComplex.mk iα pα zα
  let P := coefficientPullbackExtension H (Iso.refl S.X₃) A.g
  have hP : P.ShortExact :=
    coefficientPullbackExtension_shortExact H (Iso.refl S.X₃) A.g hα
  have hPclass : hP.extClass = (Ext.mk₀ A.g).comp hα.extClass (zero_add 1) := by
    have hc := coefficientPullbackExtension_extClass H (Iso.refl S.X₃) A.g hα
    change hP.extClass =
      ((Ext.mk₀ A.g).comp hα.extClass (zero_add 1)).comp
        (Ext.mk₀ (𝟙 S.X₃)) (add_zero 1) at hc
    exact hc.trans (Ext.comp_mk₀_id ((Ext.mk₀ A.g).comp hα.extClass (zero_add 1)))
  obtain ⟨t, hti, htp⟩ := exists_extension_comparison_of_extClass_naturality
    S.g iβ pβ zβ P.f P.g P.zero hβ hP (hroot.trans hPclass.symm)
  let m := t ≫ pullback.fst pα A.g
  have hmi : iβ ≫ m = S.g ≫ iα := by
    change iβ ≫ (t ≫ pullback.fst pα A.g) = _
    rw [← Category.assoc, hti, Category.assoc,
      coefficientPullbackExtension_f_fst, Iso.refl_hom, Category.id_comp]
  have hmp : m ≫ pα = pβ ≫ A.g := by
    change (t ≫ pullback.fst pα A.g) ≫ pα = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, htp]
  let φ : B ⟶ H :=
    { τ₁ := S.g
      τ₂ := m
      τ₃ := A.g
      comm₁₂ := hmi.symm
      comm₂₃ := hmp }
  have : Mono S.f := hS.mono_f
  have : Mono A.f := hA.mono_f
  have : Mono iβ := hβ.mono_f
  have : Epi S.g := hS.epi_g
  have hi0 : (S.f ≫ iβ) ≫ m = 0 := by
    rw [Category.assoc, hmi, ← Category.assoc, S.zero, zero_comp]
  let i : S.X₁ ⟶ kernel m := kernel.lift m (S.f ≫ iβ) hi0
  have hi : i ≫ kernel.ι m = S.f ≫ iβ := kernel.lift_ι _ _ _
  have hp0 : (kernel.ι m ≫ pβ) ≫ A.g = 0 := by
    rw [Category.assoc, ← hmp, ← Category.assoc, kernel.condition, zero_comp]
  let p : kernel m ⟶ A.X₁ := hA.exact.lift (kernel.ι m ≫ pβ) hp0
  have hp : p ≫ A.f = kernel.ι m ≫ pβ := hA.exact.lift_f _ hp0
  have hz : i ≫ p = 0 := by
    apply (cancel_mono A.f).mp
    rw [Category.assoc, hp, ← Category.assoc, hi,
      Category.assoc, zβ, comp_zero, zero_comp]
  let G := ShortComplex.mk i p hz
  let ψ : G ⟶ B :=
    { τ₁ := S.f
      τ₂ := kernel.ι m
      τ₃ := A.f
      comm₁₂ := hi.symm
      comm₂₃ := hp.symm }
  have hψφ : ψ ≫ φ = 0 := by
    ext
    · exact S.zero
    · exact kernel.condition m
    · exact A.zero
  have : Mono ψ := ⟨by
    intro Z u v huv
    apply ShortComplex.hom_ext
    · apply (cancel_mono S.f).mp
      exact congrArg (fun e => e.τ₁) huv
    · apply (cancel_mono (kernel.ι m)).mp
      exact congrArg (fun e => e.τ₂) huv
    · apply (cancel_mono A.f).mp
      exact congrArg (fun e => e.τ₃) huv⟩
  have hker : IsLimit (KernelFork.ofι ψ hψφ) := by
    apply KernelFork.IsLimit.ofι'
    intro Z k hk
    have hk₁ : k.τ₁ ≫ S.g = 0 := congrArg (fun e => e.τ₁) hk
    have hk₂ : k.τ₂ ≫ m = 0 := congrArg (fun e => e.τ₂) hk
    have hk₃ : k.τ₃ ≫ A.g = 0 := congrArg (fun e => e.τ₃) hk
    let u := hS.exact.lift k.τ₁ hk₁
    have hu : u ≫ S.f = k.τ₁ := hS.exact.lift_f _ hk₁
    let v := kernel.lift m k.τ₂ hk₂
    have hv : v ≫ kernel.ι m = k.τ₂ := kernel.lift_ι _ _ _
    let w := hA.exact.lift k.τ₃ hk₃
    have hw : w ≫ A.f = k.τ₃ := hA.exact.lift_f _ hk₃
    let l : Z ⟶ G :=
      { τ₁ := u
        τ₂ := v
        τ₃ := w
        comm₁₂ := by
          apply (cancel_mono (kernel.ι m)).mp
          rw [Category.assoc, hi, ← Category.assoc, hu, Category.assoc, hv]
          exact k.comm₁₂
        comm₂₃ := by
          apply (cancel_mono A.f).mp
          rw [Category.assoc, hp, ← Category.assoc, hv, Category.assoc, hw]
          exact k.comm₂₃ }
    refine ⟨l, ?_⟩
    ext
    · exact hu
    · exact hv
    · exact hw
  let snake : ShortComplex.SnakeInput C :=
    { L₀ := G
      L₁ := B
      L₂ := H
      L₃ := cokernel φ
      v₀₁ := ψ
      v₁₂ := φ
      v₂₃ := cokernel.π φ
      w₀₂ := hψφ
      w₁₃ := cokernel.condition φ
      h₀ := hker
      h₃ := cokernelIsCokernel φ
      L₁_exact := hβ.exact
      epi_L₁_g := hβ.epi_g
      L₂_exact := hα.exact
      mono_L₂_f := hα.mono_f }
  have : Mono G.f := mono_of_mono_fac hi
  have : Epi snake.v₂₃.τ₁ := epi_of_isColimit_cofork snake.h₃τ₁
  have hπ : snake.v₂₃.τ₁ = 0 :=
    zero_of_epi_comp S.g snake.w₁₃_τ₁
  have hzero : IsZero snake.L₃.X₁ := IsZero.of_epi_eq_zero snake.v₂₃.τ₁ hπ
  have : Epi G.g := snake.L₁'_exact.epi_f (hzero.eq_of_tgt _ _)
  have hG : G.ShortExact := { exact := snake.L₀_exact }
  let D := ShortComplex.mk ψ φ hψφ
  have hleft : (D.map ShortComplex.π₁).ShortExact := hS
  have hright : (D.map ShortComplex.π₃).ShortExact := hA
  refine ⟨kernel m, i, p, hz, hG, kernel.ι m, m,
    hmi, hmp, hi, hp.symm, kernel.condition m, ?_, ?_⟩
  · exact hG.extClass_naturality hβ ψ
  · exact CupExtensionInterchange.extClass_comp_add_eq_zero D hG hβ hα hleft hright

end EtaleCohomology
