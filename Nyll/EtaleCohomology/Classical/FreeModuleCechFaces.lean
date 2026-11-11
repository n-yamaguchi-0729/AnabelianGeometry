/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeModuleCechSheaves
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Actual faces of the original module Cech complex

The face maps retain the original edge and triangle objects. Their
alternating sums are the original free-module differentials, before
and after the actual sheafification.
-/

@[expose] public section

noncomputable section

universe v u w

open CategoryTheory Opposite

namespace EtaleCohomology

variable {C : Type u} [Category.{v} C] {P Q : C ⥤ Type w} (η : P ⟶ Q)

/-- The original first endpoint of an edge. -/
def cechEdgeFirst : cechEdgeFunctor η ⟶ P where
  app _ := ↾fun p => p.first
  naturality _ _ _ := rfl

/-- The original second endpoint of an edge. -/
def cechEdgeSecond : cechEdgeFunctor η ⟶ P where
  app _ := ↾fun p => p.second
  naturality _ _ _ := rfl

/-- The original edge joining the first two vertices of a triangle. -/
def cechTriangleEdge01 : cechTriangleFunctor η ⟶ cechEdgeFunctor η where
  app _ := ↾fun t => ⟨t.first, t.second, t.same₁⟩
  naturality _ _ _ := rfl

/-- The original edge joining the first and last vertices of a triangle. -/
def cechTriangleEdge02 : cechTriangleFunctor η ⟶ cechEdgeFunctor η where
  app _ := ↾fun t => ⟨t.first, t.third, t.same₁.trans t.same₂⟩
  naturality _ _ _ := rfl

/-- The original edge joining the last two vertices of a triangle. -/
def cechTriangleEdge12 : cechTriangleFunctor η ⟶ cechEdgeFunctor η where
  app _ := ↾fun t => ⟨t.second, t.third, t.same₂⟩
  naturality _ _ _ := rfl

theorem cechTriangleEdge02_first :
    cechTriangleEdge02 η ≫ cechEdgeFirst η =
      cechTriangleEdge01 η ≫ cechEdgeFirst η := rfl

theorem cechTriangleEdge12_first :
    cechTriangleEdge12 η ≫ cechEdgeFirst η =
      cechTriangleEdge01 η ≫ cechEdgeSecond η := rfl

variable (R : Type w) [Ring R]

/-- The original edge differential is the difference of its actual faces. -/
theorem freeModuleCechEdgeBoundaryNat_faces :
    freeModuleCechEdgeBoundaryNat R η =
      Functor.whiskerRight (cechEdgeSecond η) (ModuleCat.free R) -
        Functor.whiskerRight (cechEdgeFirst η) (ModuleCat.free R) := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.free_hom_ext
  intro p
  change freeModuleCechEdgeBoundary R (η.app V) (ModuleCat.freeMk p) =
    (ModuleCat.free R).map ((cechEdgeSecond η).app V) (ModuleCat.freeMk p) -
      (ModuleCat.free R).map ((cechEdgeFirst η).app V) (ModuleCat.freeMk p)
  rw [ModuleCat.free_map_apply, ModuleCat.free_map_apply]
  exact ModuleCat.freeDesc_apply _ p

/-- The original triangle differential is the alternating sum of
its three actual edge faces. -/
theorem freeModuleCechTriangleBoundaryNat_faces :
    freeModuleCechTriangleBoundaryNat R η =
      Functor.whiskerRight (cechTriangleEdge12 η) (ModuleCat.free R) -
        Functor.whiskerRight (cechTriangleEdge02 η) (ModuleCat.free R) +
          Functor.whiskerRight (cechTriangleEdge01 η) (ModuleCat.free R) := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.free_hom_ext
  intro t
  change freeModuleCechTriangleBoundary R (η.app V) (ModuleCat.freeMk t) =
    (ModuleCat.free R).map ((cechTriangleEdge12 η).app V) (ModuleCat.freeMk t) -
      (ModuleCat.free R).map ((cechTriangleEdge02 η).app V) (ModuleCat.freeMk t) +
        (ModuleCat.free R).map ((cechTriangleEdge01 η).app V) (ModuleCat.freeMk t)
  rw [ModuleCat.free_map_apply, ModuleCat.free_map_apply, ModuleCat.free_map_apply]
  exact ModuleCat.freeDesc_apply _ t

variable {D : Type u} [Category.{v} D] (J : GrothendieckTopology D)
  [HasSheafify J (ModuleCat.{w} R)] {P' Q' : Dᵒᵖ ⥤ Type w} (ρ : P' ⟶ Q')

/-- The actual sheafified edge differential retains the same two faces. -/
theorem freeModuleCechEdgeBoundarySheaf_faces :
    (presheafToSheaf J (ModuleCat.{w} R)).map (freeModuleCechEdgeBoundaryNat R ρ) =
      (presheafToSheaf J (ModuleCat.{w} R)).map
          (Functor.whiskerRight (cechEdgeSecond ρ) (ModuleCat.free R)) -
        (presheafToSheaf J (ModuleCat.{w} R)).map
          (Functor.whiskerRight (cechEdgeFirst ρ) (ModuleCat.free R)) := by
  rw [freeModuleCechEdgeBoundaryNat_faces, Functor.map_sub]

/-- The actual sheafified triangle differential retains its three faces. -/
theorem freeModuleCechTriangleBoundarySheaf_faces :
    (presheafToSheaf J (ModuleCat.{w} R)).map (freeModuleCechTriangleBoundaryNat R ρ) =
      (presheafToSheaf J (ModuleCat.{w} R)).map
          (Functor.whiskerRight (cechTriangleEdge12 ρ) (ModuleCat.free R)) -
        (presheafToSheaf J (ModuleCat.{w} R)).map
          (Functor.whiskerRight (cechTriangleEdge02 ρ) (ModuleCat.free R)) +
        (presheafToSheaf J (ModuleCat.{w} R)).map
          (Functor.whiskerRight (cechTriangleEdge01 ρ) (ModuleCat.free R)) := by
  rw [freeModuleCechTriangleBoundaryNat_faces, Functor.map_add, Functor.map_sub]

end EtaleCohomology
