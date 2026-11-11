/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRelations
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda

/-!
# Refinement of the actual free abelian covering complex

A map to the original covering object sends each edge and triangle to
its original vertices. These maps commute with both alternating
boundaries, before and after sheafification. Thus an actual rational
edge cochain and its vertex correction can be restricted to the same
refinement while retaining the original triangle equation.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory Opposite

namespace EtaleCohomology

variable {C : Type u} [Category.{v} C] {T V W : C}
  (f : V ⟶ T) (g : W ⟶ V)

/-- An edge of a refined cover retains its two original vertices. -/
def cechEdgeRefinement :
    cechEdgeFunctor (yoneda.map (g ≫ f)) ⟶ cechEdgeFunctor (yoneda.map f) where
  app U := ↾fun p => ⟨p.first ≫ g, p.second ≫ g, by
    change (p.first ≫ g) ≫ f = (p.second ≫ g) ≫ f
    rw [Category.assoc, Category.assoc]
    exact p.same⟩
  naturality {U U'} a := by
    apply ConcreteCategory.hom_ext
    intro p
    apply CechEdge.ext
    · exact Category.assoc a.unop p.first g
    · exact Category.assoc a.unop p.second g

/-- A triangle of a refined cover retains its three original vertices. -/
def cechTriangleRefinement :
    cechTriangleFunctor (yoneda.map (g ≫ f)) ⟶ cechTriangleFunctor (yoneda.map f) where
  app U := ↾fun t => ⟨t.first ≫ g, t.second ≫ g, t.third ≫ g, by
    change (t.first ≫ g) ≫ f = (t.second ≫ g) ≫ f
    rw [Category.assoc, Category.assoc]
    exact t.same₁, by
    change (t.second ≫ g) ≫ f = (t.third ≫ g) ≫ f
    rw [Category.assoc, Category.assoc]
    exact t.same₂⟩
  naturality {U U'} a := by
    apply ConcreteCategory.hom_ext
    intro t
    apply CechTriangle.ext
    · exact Category.assoc a.unop t.first g
    · exact Category.assoc a.unop t.second g
    · exact Category.assoc a.unop t.third g

/-- Refinement preserves the original difference of the two endpoints. -/
theorem freeCechEdgeRefinement_boundary :
    Functor.whiskerRight (cechEdgeRefinement f g) AddCommGrpCat.free ≫
        freeCechEdgeBoundaryNat (yoneda.map f) =
      freeCechEdgeBoundaryNat (yoneda.map (g ≫ f)) ≫
        Functor.whiskerRight (yoneda.map g) AddCommGrpCat.free := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro p
  change freeCechEdgeBoundary ((yoneda.map f).app U)
      (FreeAbelianGroup.map ((cechEdgeRefinement f g).app U) (FreeAbelianGroup.of p)) =
    FreeAbelianGroup.map ((yoneda.map g).app U)
      (freeCechEdgeBoundary ((yoneda.map (g ≫ f)).app U) (FreeAbelianGroup.of p))
  simp only [FreeAbelianGroup.map_of_apply, freeCechEdgeBoundary]
  rfl

/-- Refinement preserves the original alternating triangle boundary. -/
theorem freeCechTriangleRefinement_boundary :
    Functor.whiskerRight (cechTriangleRefinement f g) AddCommGrpCat.free ≫
        freeCechTriangleBoundaryNat (yoneda.map f) =
      freeCechTriangleBoundaryNat (yoneda.map (g ≫ f)) ≫
        Functor.whiskerRight (cechEdgeRefinement f g) AddCommGrpCat.free := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro t
  change freeCechTriangleBoundary ((yoneda.map f).app U)
      (FreeAbelianGroup.map ((cechTriangleRefinement f g).app U)
        (FreeAbelianGroup.of t)) =
    FreeAbelianGroup.map ((cechEdgeRefinement f g).app U)
      (freeCechTriangleBoundary ((yoneda.map (g ≫ f)).app U) (FreeAbelianGroup.of t))
  simp only [FreeAbelianGroup.map_of_apply, freeCechTriangleBoundary]
  rfl

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]

/-- The original free abelian edge sheaf under refinement. -/
def abelianCechEdgeRefinement :
    (presheafToSheaf J AddCommGrpCat.{v}).obj
        (cechEdgeFunctor (yoneda.map (g ≫ f)) ⋙ AddCommGrpCat.free) ⟶
      (presheafToSheaf J AddCommGrpCat.{v}).obj
        (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free) :=
  (presheafToSheaf J AddCommGrpCat.{v}).map
    (Functor.whiskerRight (cechEdgeRefinement f g) AddCommGrpCat.free)

/-- The original free abelian triangle sheaf under refinement. -/
def abelianCechTriangleRefinement :
    (presheafToSheaf J AddCommGrpCat.{v}).obj
        (cechTriangleFunctor (yoneda.map (g ≫ f)) ⋙ AddCommGrpCat.free) ⟶
      (presheafToSheaf J AddCommGrpCat.{v}).obj
        (cechTriangleFunctor (yoneda.map f) ⋙ AddCommGrpCat.free) :=
  (presheafToSheaf J AddCommGrpCat.{v}).map
    (Functor.whiskerRight (cechTriangleRefinement f g) AddCommGrpCat.free)

/-- Vertex corrections restrict along the same actual edge refinement. -/
theorem abelianCechEdgeRefinement_boundary :
    abelianCechEdgeRefinement f g J ≫
        (presheafToSheaf J AddCommGrpCat.{v}).map
          (freeCechEdgeBoundaryNat (yoneda.map f)) =
      (presheafToSheaf J AddCommGrpCat.{v}).map
          (freeCechEdgeBoundaryNat (yoneda.map (g ≫ f))) ≫
        (freeAbelianSheafYoneda J).map g := by
  change (presheafToSheaf J AddCommGrpCat.{v}).map _ ≫
      (presheafToSheaf J AddCommGrpCat.{v}).map _ =
    (presheafToSheaf J AddCommGrpCat.{v}).map _ ≫
      (presheafToSheaf J AddCommGrpCat.{v}).map _
  rw [← Functor.map_comp, ← Functor.map_comp, freeCechEdgeRefinement_boundary]
  rfl

/-- The actual triangle equation remains valid after refinement. -/
theorem abelianCechTriangleRefinement_boundary :
    abelianCechTriangleRefinement f g J ≫
        (presheafToSheaf J AddCommGrpCat.{v}).map
          (freeCechTriangleBoundaryNat (yoneda.map f)) =
      (presheafToSheaf J AddCommGrpCat.{v}).map
          (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫
        abelianCechEdgeRefinement f g J := by
  change (presheafToSheaf J AddCommGrpCat.{v}).map _ ≫
      (presheafToSheaf J AddCommGrpCat.{v}).map _ =
    (presheafToSheaf J AddCommGrpCat.{v}).map _ ≫
      (presheafToSheaf J AddCommGrpCat.{v}).map _
  rw [← Functor.map_comp, ← Functor.map_comp, freeCechTriangleRefinement_boundary]

end EtaleCohomology
