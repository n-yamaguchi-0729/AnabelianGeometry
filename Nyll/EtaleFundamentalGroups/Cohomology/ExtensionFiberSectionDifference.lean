/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFibers
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Actual coefficient sections measuring differences of extension lifts

The original sectionwise translation bijection supplies the coefficient
section between any two actual lifts. Its inclusion is their actual
difference. These sections restrict naturally and satisfy the original
three-lift cocycle equation, without a connectedness assumption on the
étale object or a choice of a constant coefficient value.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}}
  (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
  (t : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ S.X₃.obj ⋙ forget AddCommGrpCat.{u})
  (hS : S.ShortExact)

/-- The actual kernel section carrying the first original lift to
the second, obtained from the original sectionwise translation bijection. -/
def extensionFiberSectionDifference (U : X.Etaleᵒᵖ)
    (s₀ s₁ : (extensionFiber S t).obj.obj U) : S.X₁.obj.obj U :=
  Classical.choose ((extensionFiber_translation_bijective S t hS U s₀).surjective s₁)

/-- Inclusion of the actual difference section translates the
first original lift to the second original lift. -/
theorem extensionFiberSectionDifference_add (U : X.Etaleᵒᵖ)
    (s₀ s₁ : (extensionFiber S t).obj.obj U) :
    S.f.hom.app U (extensionFiberSectionDifference S t hS U s₀ s₁) +
        (show S.X₂.obj.obj U from s₀.val) = (show S.X₂.obj.obj U from s₁.val) :=
  congrArg Subtype.val
    (Classical.choose_spec
      ((extensionFiber_translation_bijective S t hS U s₀).surjective s₁))

/-- The coefficient section has exactly the original difference
under the original kernel inclusion. -/
theorem extensionFiberSectionDifference_inclusion (U : X.Etaleᵒᵖ)
    (s₀ s₁ : (extensionFiber S t).obj.obj U) :
    S.f.hom.app U (extensionFiberSectionDifference S t hS U s₀ s₁) =
      (show S.X₂.obj.obj U from s₁.val) - (show S.X₂.obj.obj U from s₀.val) :=
  eq_sub_iff_add_eq.mpr (extensionFiberSectionDifference_add S t hS U s₀ s₁)

/-- The original monic inclusion uniquely determines the actual
coefficient section, including on disconnected étale objects. -/
theorem extensionFiberSectionDifference_unique (U : X.Etaleᵒᵖ)
    (s₀ s₁ : (extensionFiber S t).obj.obj U) (η : S.X₁.obj.obj U)
    (hη : S.f.hom.app U η = (show S.X₂.obj.obj U from s₁.val) - (show S.X₂.obj.obj U from s₀.val)) :
    extensionFiberSectionDifference S t hS U s₀ s₁ = η := by
  have : Mono S.f := hS.mono_f
  apply (AddCommGrpCat.mono_iff_injective (S.f.hom.app U)).mp inferInstance
  exact (extensionFiberSectionDifference_inclusion S t hS U s₀ s₁).trans hη.symm

/-- Restricting two actual lifts restricts their actual difference
by the original coefficient-sheaf restriction map. -/
theorem extensionFiberSectionDifference_naturality
    {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (s₀ s₁ : (extensionFiber S t).obj.obj U) :
    S.X₁.obj.map f (extensionFiberSectionDifference S t hS U s₀ s₁) =
      extensionFiberSectionDifference S t hS V
        ((extensionFiber S t).obj.map f s₀) ((extensionFiber S t).obj.map f s₁) := by
  have : Mono S.f := hS.mono_f
  apply (AddCommGrpCat.mono_iff_injective (S.f.hom.app V)).mp inferInstance
  rw [extensionFiberSectionDifference_inclusion]
  calc
    S.f.hom.app V
        (S.X₁.obj.map f (extensionFiberSectionDifference S t hS U s₀ s₁)) =
      S.X₂.obj.map f
        (S.f.hom.app U (extensionFiberSectionDifference S t hS U s₀ s₁)) :=
      ConcreteCategory.congr_hom (S.f.hom.naturality f)
        (extensionFiberSectionDifference S t hS U s₀ s₁)
    _ = S.X₂.obj.map f ((show S.X₂.obj.obj U from s₁.val) - (show S.X₂.obj.obj U from s₀.val)) :=
      congrArg (S.X₂.obj.map f)
        (extensionFiberSectionDifference_inclusion S t hS U s₀ s₁)
    _ = _ := map_sub (S.X₂.obj.map f).hom
      (show S.X₂.obj.obj U from s₁.val) (show S.X₂.obj.obj U from s₀.val)

/-- The actual differences of three lifts satisfy the additive
cocycle equation on the same original étale object. -/
theorem extensionFiberSectionDifference_cocycle (U : X.Etaleᵒᵖ)
    (s₀ s₁ s₂ : (extensionFiber S t).obj.obj U) :
    extensionFiberSectionDifference S t hS U s₀ s₁ +
        extensionFiberSectionDifference S t hS U s₁ s₂ =
      extensionFiberSectionDifference S t hS U s₀ s₂ := by
  have : Mono S.f := hS.mono_f
  apply (AddCommGrpCat.mono_iff_injective (S.f.hom.app U)).mp inferInstance
  rw [map_add, extensionFiberSectionDifference_inclusion,
    extensionFiberSectionDifference_inclusion, extensionFiberSectionDifference_inclusion]
  exact (add_comm _ _).trans (sub_add_sub_cancel
    (show S.X₂.obj.obj U from s₂.val) (show S.X₂.obj.obj U from s₁.val)
    (show S.X₂.obj.obj U from s₀.val))

/-- The original zero difference is the zero coefficient section. -/
theorem extensionFiberSectionDifference_self (U : X.Etaleᵒᵖ)
    (s : (extensionFiber S t).obj.obj U) :
    extensionFiberSectionDifference S t hS U s s = 0 := by
  apply extensionFiberSectionDifference_unique S t hS U s s
  exact (map_zero (S.f.hom.app U).hom).trans
    (sub_self (show S.X₂.obj.obj U from s.val)).symm

end EtaleFundamentalGroups.Cohomology
