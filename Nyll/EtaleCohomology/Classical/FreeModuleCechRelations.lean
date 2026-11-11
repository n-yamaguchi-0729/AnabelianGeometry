/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRelations
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Tactic.Abel

/-!
# Exact relations in the free module Cech complex

The actual free module Cech augmentation and its first relation complex
are exact over any coefficient ring. The contraction chooses one point
in each nonempty fiber of the original map of sets. In particular no
flatness over the integers is used for finite coefficient rings.

The vertices, edges and triangles are the same objects as in
`FreeAbelianCechRelations`; the maps here use the actual free-module
functor needed for native module-sheaf Yoneda cup products.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace EtaleCohomology

variable (R : Type u) [Ring R] {A B : Type u} (f : A → B)

/-- The boundary of an actual free module edge. -/
def freeModuleCechEdgeBoundary :
    (ModuleCat.free R).obj (CechEdge f) ⟶ (ModuleCat.free R).obj A :=
  ModuleCat.freeDesc (↾fun p =>
    ModuleCat.freeMk p.second - ModuleCat.freeMk p.first)

/-- The alternating boundary of an actual free module triangle. -/
def freeModuleCechTriangleBoundary :
    (ModuleCat.free R).obj (CechTriangle f) ⟶ (ModuleCat.free R).obj (CechEdge f) :=
  ModuleCat.freeDesc (↾fun t =>
    ModuleCat.freeMk (CechEdge.mk t.second t.third t.same₂) -
    ModuleCat.freeMk (CechEdge.mk t.first t.third (t.same₁.trans t.same₂)) +
    ModuleCat.freeMk (CechEdge.mk t.first t.second t.same₁))

/-- Consecutive alternating boundaries compose to zero. -/
theorem freeModuleCechTriangle_boundary :
    freeModuleCechTriangleBoundary R f ≫ freeModuleCechEdgeBoundary R f = 0 := by
  apply ModuleCat.free_hom_ext
  intro t
  change freeModuleCechEdgeBoundary R f
      (freeModuleCechTriangleBoundary R f (ModuleCat.freeMk t)) = 0
  simp only [freeModuleCechTriangleBoundary, ModuleCat.freeDesc_apply,
    TypeCat.ofHom_apply, map_add, map_sub, freeModuleCechEdgeBoundary]
  abel

/-- Every actual free module edge cycle is a triangle boundary. -/
theorem exists_freeModuleCechTriangle_primitive
    (c : (ModuleCat.free R).obj (CechEdge f))
    (hc : freeModuleCechEdgeBoundary R f c = 0) :
    ∃ b : (ModuleCat.free R).obj (CechTriangle f),
      freeModuleCechTriangleBoundary R f b = c := by
  classical
  let r : Set.range f → A := fun b => Classical.choose b.property
  have hr (b : Set.range f) : f (r b) = b.val := Classical.choose_spec b.property
  let a : A → A := fun x => r ⟨f x, ⟨x, rfl⟩⟩
  have ha (x : A) : f (a x) = f x := hr _
  have heq (p : CechEdge f) : a p.first = a p.second := by
    apply congrArg r
    exact Subtype.ext p.same
  let s₀ : (ModuleCat.free R).obj A ⟶ (ModuleCat.free R).obj (CechEdge f) :=
    ModuleCat.freeDesc (↾fun x => ModuleCat.freeMk (CechEdge.mk (a x) x (ha x)))
  let s₁ : (ModuleCat.free R).obj (CechEdge f) ⟶
      (ModuleCat.free R).obj (CechTriangle f) :=
    ModuleCat.freeDesc (↾fun p => ModuleCat.freeMk
      (CechTriangle.mk (a p.first) p.first p.second (ha p.first) p.same))
  have h : s₁ ≫ freeModuleCechTriangleBoundary R f =
      𝟙 _ - freeModuleCechEdgeBoundary R f ≫ s₀ := by
    apply ModuleCat.free_hom_ext
    intro p
    change freeModuleCechTriangleBoundary R f (s₁ (ModuleCat.freeMk p)) =
      ModuleCat.freeMk p - s₀ (freeModuleCechEdgeBoundary R f (ModuleCat.freeMk p))
    simp only [s₁, s₀, ModuleCat.freeDesc_apply, TypeCat.ofHom_apply,
      freeModuleCechTriangleBoundary, freeModuleCechEdgeBoundary, map_sub]
    have hp : CechEdge.mk (a p.first) p.second ((ha p.first).trans p.same) =
        CechEdge.mk (a p.second) p.second (ha p.second) := by
      apply CechEdge.ext
      · exact heq p
      · rfl
    rw [hp]
    have hp' : CechEdge.mk p.first p.second p.same = p := by cases p; rfl
    rw [hp']
    abel
  refine ⟨s₁ c, ?_⟩
  have hx := ConcreteCategory.congr_hom h c
  change freeModuleCechTriangleBoundary R f (s₁ c) =
    c - s₀ (freeModuleCechEdgeBoundary R f c) at hx
  simpa only [hc, map_zero, sub_zero] using hx

/-- The original free-module augmentation kills edge boundaries. -/
theorem freeModuleCechEdge_augmentation :
    freeModuleCechEdgeBoundary R f ≫ (ModuleCat.free R).map (↾f) = 0 := by
  apply ModuleCat.free_hom_ext
  intro p
  change (ModuleCat.free R).map (↾f)
    (freeModuleCechEdgeBoundary R f (ModuleCat.freeMk p)) = 0
  simp only [freeModuleCechEdgeBoundary, ModuleCat.freeDesc_apply,
    TypeCat.ofHom_apply, map_sub, ModuleCat.free_map_apply, p.same, sub_self]

/-- Every relation in the kernel of the original augmentation is an
actual edge boundary, including over finite coefficient rings. -/
theorem exists_freeModuleCechEdge_primitive
    (c : (ModuleCat.free R).obj A)
    (hc : (ModuleCat.free R).map (↾f) c = 0) :
    ∃ b : (ModuleCat.free R).obj (CechEdge f),
      freeModuleCechEdgeBoundary R f b = c := by
  classical
  let r : Set.range f → A := fun y => Classical.choose y.property
  have hr (y : Set.range f) : f (r y) = y.val := Classical.choose_spec y.property
  let a : A → A := fun x => r ⟨f x, ⟨x, rfl⟩⟩
  have ha (x : A) : f (a x) = f x := hr _
  let s : (ModuleCat.free R).obj A ⟶ (ModuleCat.free R).obj (CechEdge f) :=
    ModuleCat.freeDesc (↾fun x => ModuleCat.freeMk (CechEdge.mk (a x) x (ha x)))
  let q : (ModuleCat.free R).obj B ⟶ (ModuleCat.free R).obj A :=
    ModuleCat.freeDesc (↾fun y =>
      if h : y ∈ Set.range f then ModuleCat.freeMk (r ⟨y, h⟩) else 0)
  have hq (x : A) : q (ModuleCat.freeMk (f x)) = ModuleCat.freeMk (a x) := by
    simp only [q, a, ModuleCat.freeDesc_apply, TypeCat.ofHom_apply,
      dite_eq_left (show f x ∈ Set.range f from ⟨x, rfl⟩)]
  have h : s ≫ freeModuleCechEdgeBoundary R f =
      𝟙 _ - (ModuleCat.free R).map (↾f) ≫ q := by
    apply ModuleCat.free_hom_ext
    intro x
    change freeModuleCechEdgeBoundary R f (s (ModuleCat.freeMk x)) =
      ModuleCat.freeMk x - q ((ModuleCat.free R).map (↾f) (ModuleCat.freeMk x))
    simp only [s, ModuleCat.freeDesc_apply, TypeCat.ofHom_apply,
      freeModuleCechEdgeBoundary, ModuleCat.free_map_apply, hq]
  refine ⟨s c, ?_⟩
  have hx := ConcreteCategory.congr_hom h c
  change freeModuleCechEdgeBoundary R f (s c) =
    c - q ((ModuleCat.free R).map (↾f) c) at hx
  simpa only [hc, map_zero, sub_zero] using hx

end EtaleCohomology
