/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.Tactic.Abel

/-!
# Relations in the free abelian Cech complex

For every map of sets, the positive-degree-one free abelian Cech complex
is exact. The contraction chooses one point in each nonempty fiber; it
does not require a section over points outside the image. This is the
pointwise algebraic input for the free abelian sheaf Cech resolution.
-/

@[expose] public section

noncomputable section

namespace EtaleCohomology

variable {A B : Type*} (f : A → B)

/-- An edge in a fiber of a map of sets. -/
@[ext]
structure CechEdge where
  /-- First endpoint. -/
  first : A
  /-- Second endpoint. -/
  second : A
  /-- Both endpoints have the same image. -/
  same : f first = f second

/-- A triangle in a fiber of a map of sets. -/
@[ext]
structure CechTriangle where
  /-- First vertex. -/
  first : A
  /-- Second vertex. -/
  second : A
  /-- Third vertex. -/
  third : A
  /-- The first two vertices have the same image. -/
  same₁ : f first = f second
  /-- The last two vertices have the same image. -/
  same₂ : f second = f third

/-- The boundary of a free abelian Cech edge. -/
def freeCechEdgeBoundary : FreeAbelianGroup (CechEdge f) →+ FreeAbelianGroup A :=
  FreeAbelianGroup.lift fun p =>
    FreeAbelianGroup.of p.second - FreeAbelianGroup.of p.first

/-- The alternating boundary of a free abelian Cech triangle. -/
def freeCechTriangleBoundary :
    FreeAbelianGroup (CechTriangle f) →+ FreeAbelianGroup (CechEdge f) :=
  FreeAbelianGroup.lift fun t =>
    FreeAbelianGroup.of ⟨t.second, t.third, t.same₂⟩ -
    FreeAbelianGroup.of ⟨t.first, t.third, t.same₁.trans t.same₂⟩ +
    FreeAbelianGroup.of ⟨t.first, t.second, t.same₁⟩

/-- The two actual alternating boundaries compose to zero. -/
theorem freeCechEdgeBoundary_triangle (c : FreeAbelianGroup (CechTriangle f)) :
    freeCechEdgeBoundary f (freeCechTriangleBoundary f c) = 0 := by
  have h : (freeCechEdgeBoundary f).comp (freeCechTriangleBoundary f) = 0 := by
    apply FreeAbelianGroup.lift_ext
    intro t
    simp only [AddMonoidHom.comp_apply, freeCechTriangleBoundary,
      FreeAbelianGroup.lift_apply_of, map_add, map_sub, freeCechEdgeBoundary,
      AddMonoidHom.zero_apply]
    abel
  exact congrArg (fun k => k c) h

/-- Every free abelian Cech edge cycle is the boundary of a triangle chain.
This is exactness, without a surjectivity hypothesis on the map of sets. -/
theorem exists_freeCechTriangle_primitive
    (c : FreeAbelianGroup (CechEdge f)) (hc : freeCechEdgeBoundary f c = 0) :
    ∃ b : FreeAbelianGroup (CechTriangle f), freeCechTriangleBoundary f b = c := by
  classical
  let r : Set.range f → A := fun b => Classical.choose b.property
  have hr (b : Set.range f) : f (r b) = b.val := Classical.choose_spec b.property
  let a : A → A := fun x => r ⟨f x, ⟨x, rfl⟩⟩
  have ha (x : A) : f (a x) = f x := hr _
  have heq (p : CechEdge f) : a p.first = a p.second := by
    apply congrArg r
    exact Subtype.ext p.same
  let s₀ : FreeAbelianGroup A →+ FreeAbelianGroup (CechEdge f) :=
    FreeAbelianGroup.lift fun x => FreeAbelianGroup.of ⟨a x, x, ha x⟩
  let s₁ : FreeAbelianGroup (CechEdge f) →+ FreeAbelianGroup (CechTriangle f) :=
    FreeAbelianGroup.lift fun p =>
      FreeAbelianGroup.of ⟨a p.first, p.first, p.second, ha p.first, p.same⟩
  have h : (freeCechTriangleBoundary f).comp s₁ =
      AddMonoidHom.id _ - s₀.comp (freeCechEdgeBoundary f) := by
    apply FreeAbelianGroup.lift_ext
    intro p
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply,
      AddMonoidHom.id_apply, s₁, s₀, FreeAbelianGroup.lift_apply_of,
      freeCechTriangleBoundary, freeCechEdgeBoundary, map_sub]
    have hp : (CechEdge.mk (a p.first) p.second ((ha p.first).trans p.same)) =
        CechEdge.mk (a p.second) p.second (ha p.second) := by
      apply CechEdge.ext
      · exact heq p
      · rfl
    rw [hp]
    have hp' : CechEdge.mk p.first p.second p.same = p := by cases p; rfl
    rw [hp']
    abel
  refine ⟨s₁ c, ?_⟩
  have hx := congrArg (fun k => k c) h
  change freeCechTriangleBoundary f (s₁ c) = c - s₀ (freeCechEdgeBoundary f c) at hx
  simpa only [hc, map_zero, sub_zero] using hx

/-- The augmentation kills each edge boundary. -/
theorem freeCechEdgeBoundary_augmentation (c : FreeAbelianGroup (CechEdge f)) :
    FreeAbelianGroup.map f (freeCechEdgeBoundary f c) = 0 := by
  have h : (FreeAbelianGroup.map f).comp (freeCechEdgeBoundary f) = 0 := by
    apply FreeAbelianGroup.lift_ext
    intro p
    simp only [AddMonoidHom.comp_apply, freeCechEdgeBoundary,
      FreeAbelianGroup.lift_apply_of, map_sub, FreeAbelianGroup.map_of_apply,
      p.same, sub_self, AddMonoidHom.zero_apply]
  exact congrArg (fun k => k c) h

/-- Every relation killed by the actual augmentation is an edge boundary.
No surjectivity of the map of sets is required. -/
theorem exists_freeCechEdge_primitive
    (c : FreeAbelianGroup A) (hc : FreeAbelianGroup.map f c = 0) :
    ∃ b : FreeAbelianGroup (CechEdge f), freeCechEdgeBoundary f b = c := by
  classical
  let r : Set.range f → A := fun y => Classical.choose y.property
  have hr (y : Set.range f) : f (r y) = y.val := Classical.choose_spec y.property
  let a : A → A := fun x => r ⟨f x, ⟨x, rfl⟩⟩
  have ha (x : A) : f (a x) = f x := hr _
  let s : FreeAbelianGroup A →+ FreeAbelianGroup (CechEdge f) :=
    FreeAbelianGroup.lift fun x => FreeAbelianGroup.of ⟨a x, x, ha x⟩
  let q : FreeAbelianGroup B →+ FreeAbelianGroup A :=
    FreeAbelianGroup.lift fun y =>
      if h : y ∈ Set.range f then FreeAbelianGroup.of (r ⟨y, h⟩) else 0
  have hq (x : A) : q (FreeAbelianGroup.of (f x)) = FreeAbelianGroup.of (a x) := by
    simp only [q, a, FreeAbelianGroup.lift_apply_of, dite_eq_left (show f x ∈ Set.range f
      from ⟨x, rfl⟩)]
  have h : (freeCechEdgeBoundary f).comp s =
      AddMonoidHom.id _ - q.comp (FreeAbelianGroup.map f) := by
    apply FreeAbelianGroup.lift_ext
    intro x
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply,
      AddMonoidHom.id_apply, s, FreeAbelianGroup.lift_apply_of,
      freeCechEdgeBoundary, FreeAbelianGroup.map_of_apply, hq]
  refine ⟨s c, ?_⟩
  have h' := congrArg (fun k => k c) h
  change freeCechEdgeBoundary f (s c) = c - q (FreeAbelianGroup.map f c) at h'
  simpa only [hc, map_zero, sub_zero] using h'

end EtaleCohomology

