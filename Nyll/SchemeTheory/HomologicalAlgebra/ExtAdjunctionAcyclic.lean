/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Copyright (c) 2026 Joël Riou. All rights reserved.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Joël Riou, Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# An Ext adjunction for an exact right adjoint and an acyclic source

The actual adjunction unit and the Ext map of the exact right adjoint
define the comparison. It is bijective when images of injectives have
vanishing higher Ext from the specified source. No exactness of the left
adjoint, and no preservation of injectives by the right adjoint, is used.

The comparison calculation generalizes `Adjunction.extEquiv` in
`Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction`; its bijectivity
uses the same existing five-lemma and Ext exact-sequence suppliers as
`Functor.mapExt_bijective_of_preservesInjectiveObjects` in `Ext.MapBijective`.
-/

@[expose] public section

noncomputable section

universe wC wD

open CategoryTheory Limits Abelian

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasExt.{wC} C] [HasExt.{wD} D]
  {L : C ⥤ D} {G : D ⥤ C} [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (adj : L ⊣ G)

/-- The original unit followed by the exact right adjoint's Ext map. -/
def extMapOfExactRight (X : C) (Y : D) (n : ℕ) :
    Ext.{wD} (L.obj X) Y n →+ Ext.{wC} X (G.obj Y) n :=
  ((Ext.mk₀ (adj.unit.app X)).precomp (G.obj Y) (zero_add n)).comp
    (G.mapExtAddHom (L.obj X) Y n)

theorem extMapOfExactRight_mk₀ (X : C) {Y : D} (f : L.obj X ⟶ Y) :
    adj.extMapOfExactRight X Y 0 (Ext.mk₀ f) =
      Ext.mk₀ (adj.homEquiv X Y f) := by
  change (Ext.mk₀ (adj.unit.app X)).comp ((Ext.mk₀ f).mapExactFunctor G) (zero_add 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, adj.homEquiv_unit]

/-- The comparison respects actual Yoneda composition in the coefficient. -/
theorem extMapOfExactRight_comp (X : C) {Y Z : D} {a b c : ℕ}
    (e : Ext.{wD} (L.obj X) Y a) (e' : Ext.{wD} Y Z b) (h : a + b = c) :
    adj.extMapOfExactRight X Z c (e.comp e' h) =
      (adj.extMapOfExactRight X Y a e).comp (e'.mapExactFunctor G) h := by
  change (Ext.mk₀ (adj.unit.app X)).comp ((e.comp e' h).mapExactFunctor G) (zero_add c) = _
  rw [Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc (Ext.mk₀ (adj.unit.app X)) (e.mapExactFunctor G)
    (e'.mapExactFunctor G) (zero_add a) h (by omega)).symm

/-- Injective-image acyclicity upgrades the original adjunction comparison
to a bijection in every degree. -/
theorem extMapOfExactRight_bijective_of_acyclic [EnoughInjectives D]
    (X : C)
    (hacyclic : ∀ (I : D) [Injective I] (n : ℕ),
      Subsingleton (Ext.{wC} X (G.obj I) (n + 1)))
    (Y : D) (n : ℕ) : Function.Bijective (adj.extMapOfExactRight X Y n) := by
  induction n generalizing Y with
  | zero =>
      constructor
      · intro a b hab
        obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective (L.obj X) Y).surjective a
        obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (L.obj X) Y).surjective b
        apply congrArg Ext.mk₀
        apply (adj.homEquiv X Y).injective
        apply (Ext.mk₀_bijective X (G.obj Y)).injective
        exact (adj.extMapOfExactRight_mk₀ X f).symm.trans
          (hab.trans (adj.extMapOfExactRight_mk₀ X g))
      · intro a
        obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X (G.obj Y)).surjective a
        refine ⟨Ext.mk₀ ((adj.homEquiv X Y).symm f), ?_⟩
        rw [extMapOfExactRight_mk₀, Equiv.apply_symm_apply]
  | succ n hn =>
      let I : InjectivePresentation Y := Classical.arbitrary _
      let S := I.shortComplex
      have hS : S.ShortExact := I.shortExact_shortComplex
      have hI : Subsingleton (Ext.{wC} X (G.obj S.X₂) (n + 1)) :=
        hacyclic I.J n
      refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
        ((Ext.mk₀ S.g).postcomp (L.obj X) (add_zero n))
        (hS.extClass.postcomp (L.obj X) rfl)
        ((Ext.mk₀ (G.map S.g)).postcomp X (add_zero n))
        ((hS.map G).extClass.postcomp X rfl)
        (adj.extMapOfExactRight X S.X₂ n)
        (adj.extMapOfExactRight X S.X₃ n)
        (adj.extMapOfExactRight X S.X₁ (n + 1)) ?_ ?_
        ((ShortComplex.ab_exact_iff_function_exact _).mp
          (Ext.covariant_sequence_exact₃' (L.obj X) hS n (n + 1) rfl))
        ((ShortComplex.ab_exact_iff_function_exact _).mp
          (Ext.covariant_sequence_exact₃' X (hS.map G) n (n + 1) rfl))
        (hn S.X₂).surjective (hn S.X₃) ?_ ?_
      · apply AddMonoidHom.ext
        intro e
        change (adj.extMapOfExactRight X S.X₂ n e).comp
          (Ext.mk₀ (G.map S.g)) (add_zero n) =
          adj.extMapOfExactRight X S.X₃ n (e.comp (Ext.mk₀ S.g) (add_zero n))
        rw [extMapOfExactRight_comp, Ext.mapExactFunctor_mk₀]
      · apply AddMonoidHom.ext
        intro e
        change (adj.extMapOfExactRight X S.X₃ n e).comp (hS.map G).extClass rfl =
          adj.extMapOfExactRight X S.X₁ (n + 1) (e.comp hS.extClass rfl)
        rw [extMapOfExactRight_comp, Ext.mapExactFunctor_extClass]
      · intro e
        exact Ext.covariant_sequence_exact₁ (L.obj X) hS e
          (Ext.eq_zero_of_injective _) rfl
      · intro e
        exact Ext.covariant_sequence_exact₁ X (hS.map G) e (hI.elim _ _) rfl

end CategoryTheory.Adjunction
