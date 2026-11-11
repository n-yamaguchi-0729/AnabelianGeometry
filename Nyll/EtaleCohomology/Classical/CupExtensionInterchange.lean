/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# The actual extension-class interchange in a commutative three-by-three diagram

The two composites of boundary extension classes in a commutative
three-by-three diagram add to zero. The proof constructs the actual
pullback of the two maps to the lower-right corner. Its two relevant
short exact sequences have respectively the upper-left corner and the
sum of the other two outer corners as kernels. Naturality of the native
Ext class and the native binary-biproduct decomposition then give the
sign.

All the auxiliary short exact sequences are proved from the original
diagram. This supplies the degree-one interchange used for the actual
tensor diagram of two extensions of the constant regular sheaf.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory Limits Abelian Preadditive

namespace EtaleCohomology.CupExtensionInterchange

variable {C : Type u} [Category.{v} C] [Abelian C]

private abbrev Corner (D : ShortComplex (ShortComplex C)) : C :=
  pullback D.g.τ₃ D.X₃.g

private def middle (D : ShortComplex (ShortComplex C)) : D.X₂.X₂ ⟶ Corner D :=
  pullback.lift D.X₂.g D.g.τ₂ D.g.comm₂₃.symm

private theorem middle_fst (D : ShortComplex (ShortComplex C)) :
    middle D ≫ pullback.fst D.g.τ₃ D.X₃.g = D.X₂.g :=
  pullback.lift_fst _ _ _

private theorem middle_snd (D : ShortComplex (ShortComplex C)) :
    middle D ≫ pullback.snd D.g.τ₃ D.X₃.g = D.g.τ₂ :=
  pullback.lift_snd _ _ _

private def fromTop (D : ShortComplex (ShortComplex C)) : D.X₁.X₃ ⟶ Corner D :=
  pullback.lift D.f.τ₃ 0 (by
    have hz₃ : D.f.τ₃ ≫ D.g.τ₃ = 0 := (D.map ShortComplex.π₃).zero
    rw [hz₃, zero_comp])

private def fromLeft (D : ShortComplex (ShortComplex C)) : D.X₃.X₁ ⟶ Corner D :=
  pullback.lift 0 D.X₃.f (by rw [zero_comp, D.X₃.zero])

private def upperSequence (D : ShortComplex (ShortComplex C)) : ShortComplex C :=
  ShortComplex.mk (D.f.τ₁ ≫ D.X₂.f) (middle D) (by
    have hz₁ : D.f.τ₁ ≫ D.g.τ₁ = 0 := (D.map ShortComplex.π₁).zero
    apply pullback.hom_ext
    · rw [Category.assoc, middle_fst, Category.assoc, D.X₂.zero,
        comp_zero, zero_comp]
    · rw [Category.assoc, middle_snd, Category.assoc, ← D.g.comm₁₂,
        ← Category.assoc, hz₁, zero_comp, zero_comp])

private def bottomPullback (D : ShortComplex (ShortComplex C)) : ShortComplex C :=
  ShortComplex.mk (fromLeft D) (pullback.fst D.g.τ₃ D.X₃.g)
    (pullback.lift_fst _ _ _)

private theorem bottomPullback_shortExact (D : ShortComplex (ShortComplex C))
    (h₃ : D.X₃.ShortExact) : (bottomPullback D).ShortExact := by
  let P := ShortComplex.mk (fromLeft D) (pullback.fst D.g.τ₃ D.X₃.g)
    (pullback.lift_fst _ _ _)
  have : Mono D.X₃.f := h₃.mono_f
  have : Epi D.X₃.g := h₃.epi_g
  have hmono : Mono P.f := mono_of_mono_fac
    (show fromLeft D ≫ pullback.snd D.g.τ₃ D.X₃.g = D.X₃.f from
      pullback.lift_snd _ _ _)
  have hkernel : IsLimit (KernelFork.ofι P.f
      P.zero) := by
    apply KernelFork.IsLimit.ofι'
    intro Z k hk
    have hk' : (k ≫ pullback.snd D.g.τ₃ D.X₃.g) ≫ D.X₃.g = 0 := by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]
      change (k ≫ P.g) ≫ D.g.τ₃ = 0
      rw [hk, zero_comp]
    refine ⟨h₃.exact.lift _ hk', ?_⟩
    apply pullback.hom_ext
    · change (h₃.exact.lift _ hk' ≫ pullback.lift 0 D.X₃.f _) ≫
        pullback.fst D.g.τ₃ D.X₃.g = k ≫ P.g
      rw [Category.assoc, pullback.lift_fst, comp_zero]
      exact hk.symm
    · change (h₃.exact.lift _ hk' ≫ pullback.lift 0 D.X₃.f _) ≫
        pullback.snd D.g.τ₃ D.X₃.g = k ≫ pullback.snd D.g.τ₃ D.X₃.g
      rw [Category.assoc, pullback.lift_snd, ShortComplex.Exact.lift_f]
  exact
    { exact := P.exact_of_f_is_kernel hkernel
      mono_f := hmono
      epi_g := inferInstanceAs (Epi (pullback.fst D.g.τ₃ D.X₃.g)) }

private def middleToBottomPullback (D : ShortComplex (ShortComplex C)) :
    D.X₂ ⟶ bottomPullback D where
  τ₁ := D.g.τ₁
  τ₂ := middle D
  τ₃ := 𝟙 _
  comm₁₂ := by
    apply pullback.hom_ext
    · change (D.g.τ₁ ≫ pullback.lift 0 D.X₃.f _) ≫
        pullback.fst D.g.τ₃ D.X₃.g = (D.X₂.f ≫ middle D) ≫
          pullback.fst D.g.τ₃ D.X₃.g
      rw [Category.assoc, pullback.lift_fst, comp_zero,
        Category.assoc, middle_fst, D.X₂.zero]
    · change (D.g.τ₁ ≫ pullback.lift 0 D.X₃.f _) ≫
        pullback.snd D.g.τ₃ D.X₃.g = (D.X₂.f ≫ middle D) ≫
          pullback.snd D.g.τ₃ D.X₃.g
      rw [Category.assoc, pullback.lift_snd, Category.assoc, middle_snd]
      exact D.g.comm₁₂
  comm₂₃ := by
    change middle D ≫ pullback.fst D.g.τ₃ D.X₃.g = D.X₂.g ≫ 𝟙 _
    rw [middle_fst, Category.comp_id]

private theorem upperSequence_shortExact (D : ShortComplex (ShortComplex C))
    (h₂ : D.X₂.ShortExact) (h₃ : D.X₃.ShortExact)
    (hL : (D.map ShortComplex.π₁).ShortExact) :
    (upperSequence D).ShortExact := by
  have hz₁ : D.f.τ₁ ≫ D.g.τ₁ = 0 := (D.map ShortComplex.π₁).zero
  let L := ShortComplex.mk D.f.τ₁ D.g.τ₁ hz₁
  have hLnative : L.ShortExact := hL
  let P := ShortComplex.mk (D.f.τ₁ ≫ D.X₂.f) (middle D)
    (show (D.f.τ₁ ≫ D.X₂.f) ≫ middle D = 0 from (upperSequence D).zero)
  have : Mono D.f.τ₁ := hLnative.mono_f
  have : Mono D.X₂.f := h₂.mono_f
  have : Mono D.X₃.f := h₃.mono_f
  have hmono : Mono P.f := inferInstance
  have hepi : Epi P.g :=
    ShortComplex.epi_of_epi_of_epi_of_epi (middleToBottomPullback D)
      (bottomPullback_shortExact D h₃).exact h₂.epi_g hLnative.epi_g
      (inferInstance : Epi (𝟙 D.X₂.X₃))
  have hkernel : IsLimit (KernelFork.ofι P.f
      P.zero) := by
    apply KernelFork.IsLimit.ofι'
    intro Z k hk
    have hk₂ : k ≫ D.X₂.g = 0 := by
      calc
        k ≫ D.X₂.g = (k ≫ middle D) ≫ pullback.fst D.g.τ₃ D.X₃.g := by
          rw [Category.assoc, middle_fst]
        _ = 0 := by rw [hk, zero_comp]
    have hk₃ : k ≫ D.g.τ₂ = 0 := by
      calc
        k ≫ D.g.τ₂ = (k ≫ middle D) ≫ pullback.snd D.g.τ₃ D.X₃.g := by
          rw [Category.assoc, middle_snd]
        _ = 0 := by rw [hk, zero_comp]
    let l : Z ⟶ D.X₂.X₁ := h₂.exact.lift k hk₂
    have hl : l ≫ D.g.τ₁ = 0 := by
      apply (cancel_mono D.X₃.f).1
      calc
        (l ≫ D.g.τ₁) ≫ D.X₃.f = (l ≫ D.X₂.f) ≫ D.g.τ₂ := by
          rw [Category.assoc, D.g.comm₁₂, ← Category.assoc]
        _ = k ≫ D.g.τ₂ := by rw [ShortComplex.Exact.lift_f]
        _ = 0 ≫ D.X₃.f := by rw [hk₃, zero_comp]
    refine ⟨hLnative.exact.lift l hl, ?_⟩
    change hLnative.exact.lift l hl ≫ (D.f.τ₁ ≫ D.X₂.f) = k
    rw [← Category.assoc, ShortComplex.Exact.lift_f]
    exact h₂.exact.lift_f k hk₂
  exact
    { exact := P.exact_of_f_is_kernel hkernel
      mono_f := hmono
      epi_g := hepi }

private def lowerKernel (D : ShortComplex (ShortComplex C)) :
    D.X₁.X₃ ⊞ D.X₃.X₁ ⟶ Corner D :=
  pullback.lift (biprod.fst ≫ D.f.τ₃) (biprod.snd ≫ D.X₃.f) (by
    have hz₃ : D.f.τ₃ ≫ D.g.τ₃ = 0 := (D.map ShortComplex.π₃).zero
    rw [Category.assoc, hz₃, comp_zero,
      Category.assoc, D.X₃.zero, comp_zero])

private theorem lowerKernel_fst (D : ShortComplex (ShortComplex C)) :
    lowerKernel D ≫ pullback.fst D.g.τ₃ D.X₃.g = biprod.fst ≫ D.f.τ₃ :=
  pullback.lift_fst _ _ _

private theorem lowerKernel_snd (D : ShortComplex (ShortComplex C)) :
    lowerKernel D ≫ pullback.snd D.g.τ₃ D.X₃.g = biprod.snd ≫ D.X₃.f :=
  pullback.lift_snd _ _ _

private theorem inl_lowerKernel (D : ShortComplex (ShortComplex C)) :
    biprod.inl ≫ lowerKernel D = fromTop D := by
  apply pullback.hom_ext
  · change (biprod.inl ≫ lowerKernel D) ≫ pullback.fst D.g.τ₃ D.X₃.g =
      pullback.lift D.f.τ₃ 0 _ ≫ pullback.fst D.g.τ₃ D.X₃.g
    rw [Category.assoc, lowerKernel_fst, ← Category.assoc,
      biprod.inl_fst, Category.id_comp, pullback.lift_fst]
  · change (biprod.inl ≫ lowerKernel D) ≫ pullback.snd D.g.τ₃ D.X₃.g =
      pullback.lift D.f.τ₃ 0 _ ≫ pullback.snd D.g.τ₃ D.X₃.g
    rw [Category.assoc, lowerKernel_snd, ← Category.assoc,
      biprod.inl_snd, zero_comp, pullback.lift_snd]

private theorem inr_lowerKernel (D : ShortComplex (ShortComplex C)) :
    biprod.inr ≫ lowerKernel D = fromLeft D := by
  apply pullback.hom_ext
  · change (biprod.inr ≫ lowerKernel D) ≫ pullback.fst D.g.τ₃ D.X₃.g =
      pullback.lift 0 D.X₃.f _ ≫ pullback.fst D.g.τ₃ D.X₃.g
    rw [Category.assoc, lowerKernel_fst, ← Category.assoc,
      biprod.inr_fst, zero_comp, pullback.lift_fst]
  · change (biprod.inr ≫ lowerKernel D) ≫ pullback.snd D.g.τ₃ D.X₃.g =
      pullback.lift 0 D.X₃.f _ ≫ pullback.snd D.g.τ₃ D.X₃.g
    rw [Category.assoc, lowerKernel_snd, ← Category.assoc,
      biprod.inr_snd, Category.id_comp, pullback.lift_snd]

private def lowerSequence (D : ShortComplex (ShortComplex C)) : ShortComplex C :=
  ShortComplex.mk (lowerKernel D) (pullback.fst D.g.τ₃ D.X₃.g ≫ D.g.τ₃) (by
    have hz₃ : D.f.τ₃ ≫ D.g.τ₃ = 0 := (D.map ShortComplex.π₃).zero
    rw [← Category.assoc, lowerKernel_fst, Category.assoc, hz₃, comp_zero])

private theorem lowerSequence_shortExact (D : ShortComplex (ShortComplex C))
    (h₃ : D.X₃.ShortExact) (hR : (D.map ShortComplex.π₃).ShortExact) :
    (lowerSequence D).ShortExact := by
  have hz₃ : D.f.τ₃ ≫ D.g.τ₃ = 0 := (D.map ShortComplex.π₃).zero
  let R := ShortComplex.mk D.f.τ₃ D.g.τ₃ hz₃
  have hRnative : R.ShortExact := hR
  let P := ShortComplex.mk (lowerKernel D) (pullback.fst D.g.τ₃ D.X₃.g ≫ D.g.τ₃)
    (show lowerKernel D ≫ (pullback.fst D.g.τ₃ D.X₃.g ≫ D.g.τ₃) = 0 from
      (lowerSequence D).zero)
  have : Mono D.f.τ₃ := hRnative.mono_f
  have : Mono D.X₃.f := h₃.mono_f
  have : Epi D.g.τ₃ := hRnative.epi_g
  have : Epi D.X₃.g := h₃.epi_g
  have hmono : Mono (lowerKernel D) := by
    apply Preadditive.mono_of_cancel_zero
    intro Z k hk
    apply biprod.hom_ext
    · apply (cancel_mono D.f.τ₃).1
      calc
        (k ≫ biprod.fst) ≫ D.f.τ₃ = (k ≫ lowerKernel D) ≫
            pullback.fst D.g.τ₃ D.X₃.g := by
          rw [Category.assoc, Category.assoc, lowerKernel_fst]
        _ = (0 ≫ biprod.fst) ≫ D.f.τ₃ := by rw [hk, zero_comp, zero_comp, zero_comp]
    · apply (cancel_mono D.X₃.f).1
      calc
        (k ≫ biprod.snd) ≫ D.X₃.f = (k ≫ lowerKernel D) ≫
            pullback.snd D.g.τ₃ D.X₃.g := by
          rw [Category.assoc, Category.assoc, lowerKernel_snd]
        _ = (0 ≫ biprod.snd) ≫ D.X₃.f := by rw [hk, zero_comp, zero_comp, zero_comp]
  have hkernel : IsLimit (KernelFork.ofι P.f
      P.zero) := by
    apply KernelFork.IsLimit.ofι'
    intro Z k hk
    have hkR : (k ≫ pullback.fst D.g.τ₃ D.X₃.g) ≫ D.g.τ₃ = 0 := by
      rw [Category.assoc]
      exact hk
    have hk₃ : (k ≫ pullback.snd D.g.τ₃ D.X₃.g) ≫ D.X₃.g = 0 := by
      rw [Category.assoc, ← pullback.condition]
      exact hk
    let a : Z ⟶ D.X₁.X₃ := hRnative.exact.lift _ hkR
    let b : Z ⟶ D.X₃.X₁ := h₃.exact.lift _ hk₃
    refine ⟨biprod.lift a b, ?_⟩
    apply pullback.hom_ext
    · change (biprod.lift a b ≫ lowerKernel D) ≫ pullback.fst D.g.τ₃ D.X₃.g =
        k ≫ pullback.fst D.g.τ₃ D.X₃.g
      rw [Category.assoc, lowerKernel_fst, ← Category.assoc, biprod.lift_fst]
      exact hRnative.exact.lift_f _ hkR
    · change (biprod.lift a b ≫ lowerKernel D) ≫ pullback.snd D.g.τ₃ D.X₃.g =
        k ≫ pullback.snd D.g.τ₃ D.X₃.g
      rw [Category.assoc, lowerKernel_snd, ← Category.assoc, biprod.lift_snd]
      exact h₃.exact.lift_f _ hk₃
  exact
    { exact := P.exact_of_f_is_kernel hkernel
      mono_f := hmono
      epi_g := inferInstanceAs (Epi (pullback.fst D.g.τ₃ D.X₃.g ≫ D.g.τ₃)) }

private def topToUpper (D : ShortComplex (ShortComplex C)) :
    D.X₁ ⟶ upperSequence D where
  τ₁ := 𝟙 _
  τ₂ := D.f.τ₂
  τ₃ := fromTop D
  comm₁₂ := by
    change 𝟙 _ ≫ (D.f.τ₁ ≫ D.X₂.f) = D.X₁.f ≫ D.f.τ₂
    rw [Category.id_comp]
    exact D.f.comm₁₂
  comm₂₃ := by
    apply pullback.hom_ext
    · change (D.f.τ₂ ≫ middle D) ≫ pullback.fst D.g.τ₃ D.X₃.g =
        (D.X₁.g ≫ pullback.lift D.f.τ₃ 0 _) ≫ pullback.fst D.g.τ₃ D.X₃.g
      rw [Category.assoc, middle_fst, Category.assoc, pullback.lift_fst]
      exact D.f.comm₂₃
    · change (D.f.τ₂ ≫ middle D) ≫ pullback.snd D.g.τ₃ D.X₃.g =
        (D.X₁.g ≫ pullback.lift D.f.τ₃ 0 _) ≫ pullback.snd D.g.τ₃ D.X₃.g
      have hz₂ : D.f.τ₂ ≫ D.g.τ₂ = 0 := (D.map ShortComplex.π₂).zero
      rw [Category.assoc, middle_snd, hz₂,
        Category.assoc, pullback.lift_snd, comp_zero]

private def leftToUpper (D : ShortComplex (ShortComplex C)) :
    D.map ShortComplex.π₁ ⟶ upperSequence D where
  τ₁ := 𝟙 _
  τ₂ := D.X₂.f
  τ₃ := fromLeft D
  comm₁₂ := by
    change 𝟙 _ ≫ (D.f.τ₁ ≫ D.X₂.f) = D.f.τ₁ ≫ D.X₂.f
    exact Category.id_comp _
  comm₂₃ := (middleToBottomPullback D).comm₁₂.symm

private def lowerToRight (D : ShortComplex (ShortComplex C)) :
    lowerSequence D ⟶ D.map ShortComplex.π₃ where
  τ₁ := biprod.fst
  τ₂ := pullback.fst D.g.τ₃ D.X₃.g
  τ₃ := 𝟙 _
  comm₁₂ := (lowerKernel_fst D).symm
  comm₂₃ := by
    change pullback.fst D.g.τ₃ D.X₃.g ≫ D.g.τ₃ =
      (pullback.fst D.g.τ₃ D.X₃.g ≫ D.g.τ₃) ≫ 𝟙 _
    exact (Category.comp_id _).symm

private def lowerToBottom (D : ShortComplex (ShortComplex C)) :
    lowerSequence D ⟶ D.X₃ where
  τ₁ := biprod.snd
  τ₂ := pullback.snd D.g.τ₃ D.X₃.g
  τ₃ := 𝟙 _
  comm₁₂ := (lowerKernel_snd D).symm
  comm₂₃ := by
    change pullback.snd D.g.τ₃ D.X₃.g ≫ D.X₃.g =
      (pullback.fst D.g.τ₃ D.X₃.g ≫ D.g.τ₃) ≫ 𝟙 _
    rw [Category.comp_id]
    exact pullback.condition.symm

/-- In an actual commutative three-by-three diagram, with short exact
rows and outer columns, the two composites of the native boundary
extension classes add to zero. The middle column is already a complex
by the type of `D`; its exactness is not needed. -/
theorem extClass_comp_add_eq_zero [HasExt.{w} C]
    (D : ShortComplex (ShortComplex C))
    (h₁ : D.X₁.ShortExact) (h₂ : D.X₂.ShortExact) (h₃ : D.X₃.ShortExact)
    (hL : (D.map ShortComplex.π₁).ShortExact)
    (hR : (D.map ShortComplex.π₃).ShortExact) :
    let cR : Ext.{w} D.X₃.X₃ D.X₁.X₃ 1 := hR.extClass
    let cL : Ext.{w} D.X₃.X₁ D.X₁.X₁ 1 := hL.extClass
    cR.comp h₁.extClass (show 1 + 1 = 2 from rfl) +
      h₃.extClass.comp cL (show 1 + 1 = 2 from rfl) = 0 := by
  intro cR cL
  have hU := upperSequence_shortExact D h₂ h₃ hL
  have hV := lowerSequence_shortExact D h₃ hR
  let cU : Ext.{w} (Corner D) D.X₁.X₁ 1 := hU.extClass
  let cV : Ext.{w} D.X₃.X₃ (D.X₁.X₃ ⊞ D.X₃.X₁) 1 := hV.extClass
  have htop : (Ext.mk₀ (fromTop D)).comp cU (zero_add 1) = h₁.extClass := by
    have hn := (h₁.extClass_naturality hU (topToUpper D)).symm
    change (Ext.mk₀ (fromTop D)).comp cU (zero_add 1) =
      h₁.extClass.comp (Ext.mk₀ (𝟙 D.X₁.X₁)) (add_zero 1) at hn
    exact hn.trans (Ext.comp_mk₀_id h₁.extClass)
  have hleft : (Ext.mk₀ (fromLeft D)).comp cU (zero_add 1) = cL := by
    have hn := (hL.extClass_naturality hU (leftToUpper D)).symm
    change (Ext.mk₀ (fromLeft D)).comp cU (zero_add 1) =
      cL.comp (Ext.mk₀ (𝟙 D.X₁.X₁)) (add_zero 1) at hn
    exact hn.trans (Ext.comp_mk₀_id cL)
  have hright : cV.comp (Ext.mk₀ biprod.fst) (add_zero 1) = cR := by
    have hn := hV.extClass_naturality hR (lowerToRight D)
    change cV.comp (Ext.mk₀ biprod.fst) (add_zero 1) =
      (Ext.mk₀ (𝟙 D.X₃.X₃)).comp cR (zero_add 1) at hn
    exact hn.trans (Ext.mk₀_id_comp cR)
  have hbottom : cV.comp (Ext.mk₀ biprod.snd) (add_zero 1) = h₃.extClass := by
    have hn := hV.extClass_naturality h₃ (lowerToBottom D)
    change cV.comp (Ext.mk₀ biprod.snd) (add_zero 1) =
      (Ext.mk₀ (𝟙 D.X₃.X₃)).comp h₃.extClass (zero_add 1) at hn
    exact hn.trans (Ext.mk₀_id_comp h₃.extClass)
  have hdecomp :
      (Ext.mk₀ biprod.fst).comp h₁.extClass (zero_add 1) +
        (Ext.mk₀ biprod.snd).comp cL (zero_add 1) =
      (Ext.mk₀ (lowerKernel D)).comp cU (zero_add 1) := by
    have h := Ext.biprodAddEquiv.symm_apply_apply
      ((Ext.mk₀ (lowerKernel D)).comp cU (zero_add 1))
    change
      (Ext.mk₀ biprod.fst).comp
          ((Ext.mk₀ biprod.inl).comp
            ((Ext.mk₀ (lowerKernel D)).comp cU (zero_add 1)) (zero_add 1))
          (zero_add 1) +
        (Ext.mk₀ biprod.snd).comp
          ((Ext.mk₀ biprod.inr).comp
            ((Ext.mk₀ (lowerKernel D)).comp cU (zero_add 1)) (zero_add 1))
          (zero_add 1) = _ at h
    rw [Ext.mk₀_comp_mk₀_assoc biprod.inl (lowerKernel D) cU,
      inl_lowerKernel, htop,
      Ext.mk₀_comp_mk₀_assoc biprod.inr (lowerKernel D) cU,
      inr_lowerKernel, hleft] at h
    exact h
  calc
    cR.comp h₁.extClass rfl + h₃.extClass.comp cL rfl =
        (cV.comp (Ext.mk₀ biprod.fst) (add_zero 1)).comp h₁.extClass rfl +
          (cV.comp (Ext.mk₀ biprod.snd) (add_zero 1)).comp cL rfl := by
      rw [hright, hbottom]
    _ = cV.comp
        ((Ext.mk₀ biprod.fst).comp h₁.extClass (zero_add 1) +
          (Ext.mk₀ biprod.snd).comp cL (zero_add 1)) rfl := by
      rw [Ext.comp_add, Ext.comp_assoc_of_second_deg_zero,
        Ext.comp_assoc_of_second_deg_zero]
    _ = cV.comp ((Ext.mk₀ (lowerKernel D)).comp cU (zero_add 1)) rfl := by
      rw [hdecomp]
    _ = 0 := hV.extClass_comp_assoc hU.extClass

end EtaleCohomology.CupExtensionInterchange
