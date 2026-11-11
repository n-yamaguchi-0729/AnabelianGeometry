/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRelations
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeModuleCechFaces
public import Nyll.EtaleCohomology.Classical.FreeModuleCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCochains

/-!
# Original Cech boundaries under the actual coefficient comparison

The canonical free abelian to free module map commutes with the
original alternating edge and triangle boundaries. Consequently the
actual cochain equivalence preserves cocycles and differences, with
the unchanged convention second minus first. This permits root
differences in actual abelian extensions to be used in the original
module cup calculation without a module structure on those extensions.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology

variable (X : Scheme.{u}) {P Q : X.Etaleᵒᵖ ⥤ Type u} (η : P ⟶ Q)

/-- The original abelian edge boundary uses the same two faces. -/
theorem freeCechEdgeBoundaryNat_faces :
    freeCechEdgeBoundaryNat η =
      Functor.whiskerRight (cechEdgeSecond η) AddCommGrpCat.free -
        Functor.whiskerRight (cechEdgeFirst η) AddCommGrpCat.free := by
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro p
  change freeCechEdgeBoundary (η.app V) (FreeAbelianGroup.of p) =
    FreeAbelianGroup.map ((cechEdgeSecond η).app V) (FreeAbelianGroup.of p) -
      FreeAbelianGroup.map ((cechEdgeFirst η).app V) (FreeAbelianGroup.of p)
  rw [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.map_of_apply]
  exact FreeAbelianGroup.lift_apply_of _ p

/-- The original abelian triangle boundary has the same signs. -/
theorem freeCechTriangleBoundaryNat_faces :
    freeCechTriangleBoundaryNat η =
      Functor.whiskerRight (cechTriangleEdge12 η) AddCommGrpCat.free -
        Functor.whiskerRight (cechTriangleEdge02 η) AddCommGrpCat.free +
          Functor.whiskerRight (cechTriangleEdge01 η) AddCommGrpCat.free := by
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro t
  change freeCechTriangleBoundary (η.app V) (FreeAbelianGroup.of t) =
    FreeAbelianGroup.map ((cechTriangleEdge12 η).app V) (FreeAbelianGroup.of t) -
      FreeAbelianGroup.map ((cechTriangleEdge02 η).app V) (FreeAbelianGroup.of t) +
        FreeAbelianGroup.map ((cechTriangleEdge01 η).app V) (FreeAbelianGroup.of t)
  rw [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.map_of_apply,
    FreeAbelianGroup.map_of_apply]
  exact FreeAbelianGroup.lift_apply_of _ t

theorem freeCechEdgeBoundarySheaf_faces :
    (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (freeCechEdgeBoundaryNat η) =
      (freeAbelianSheafFunctor X).map (cechEdgeSecond η) -
        (freeAbelianSheafFunctor X).map (cechEdgeFirst η) := by
  rw [freeCechEdgeBoundaryNat_faces, Functor.map_sub]
  rfl

theorem freeCechTriangleBoundarySheaf_faces :
    (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (freeCechTriangleBoundaryNat η) =
      (freeAbelianSheafFunctor X).map (cechTriangleEdge12 η) -
        (freeAbelianSheafFunctor X).map (cechTriangleEdge02 η) +
          (freeAbelianSheafFunctor X).map (cechTriangleEdge01 η) := by
  rw [freeCechTriangleBoundaryNat_faces, Functor.map_add, Functor.map_sub]
  rfl

variable (R : Type u) [CommRing R]

/-- The same generator map commutes with the original edge boundary. -/
theorem freeModuleSheafIntegerMap_edgeBoundary :
    (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (freeCechEdgeBoundaryNat η) ≫ freeModuleSheafIntegerMap X R P =
      freeModuleSheafIntegerMap X R (cechEdgeFunctor η) ≫
        (Classical.forgetCoefficients.{u + 1, u, u, u}
          (J := X.smallEtaleTopology) (R := R)).map
            ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
          (freeModuleCechEdgeBoundaryNat R η)) := by
  rw [freeCechEdgeBoundarySheaf_faces, freeModuleCechEdgeBoundarySheaf_faces,
    Functor.map_sub, Preadditive.sub_comp, Preadditive.comp_sub]
  exact congrArg₂ (fun a b => a - b)
    (freeModuleSheafIntegerMap_naturality X R (cechEdgeSecond η))
    (freeModuleSheafIntegerMap_naturality X R (cechEdgeFirst η))

/-- The same generator map commutes with the original triangle boundary. -/
theorem freeModuleSheafIntegerMap_triangleBoundary :
    (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (freeCechTriangleBoundaryNat η) ≫
      freeModuleSheafIntegerMap X R (cechEdgeFunctor η) =
      freeModuleSheafIntegerMap X R (cechTriangleFunctor η) ≫
        (Classical.forgetCoefficients.{u + 1, u, u, u}
          (J := X.smallEtaleTopology) (R := R)).map
            ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
          (freeModuleCechTriangleBoundaryNat R η)) := by
  rw [freeCechTriangleBoundarySheaf_faces, freeModuleCechTriangleBoundarySheaf_faces,
    Functor.map_add, Functor.map_sub, Preadditive.add_comp, Preadditive.sub_comp,
    Preadditive.comp_add, Preadditive.comp_sub]
  exact congrArg₂ (fun a b => a + b)
    (congrArg₂ (fun a b => a - b)
      (freeModuleSheafIntegerMap_naturality X R (cechTriangleEdge12 η))
      (freeModuleSheafIntegerMap_naturality X R (cechTriangleEdge02 η)))
    (freeModuleSheafIntegerMap_naturality X R (cechTriangleEdge01 η))

/-- Original vertex differences are retained by the actual cochain
comparison. -/
theorem freeModuleSheafUnderlyingHomEquiv_edgeBoundary
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (b : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    freeModuleSheafUnderlyingHomEquiv X R (cechEdgeFunctor η) F
        ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
          (freeModuleCechEdgeBoundaryNat R η) ≫ b) =
      (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (freeCechEdgeBoundaryNat η) ≫ freeModuleSheafUnderlyingHomEquiv X R P F b := by
  rw [freeModuleSheafUnderlyingHomEquiv_eq, Functor.map_comp, ← Category.assoc,
    ← freeModuleSheafIntegerMap_edgeBoundary, Category.assoc,
    ← freeModuleSheafUnderlyingHomEquiv_eq]

/-- Original triangle boundaries are retained by the same cochain
comparison. -/
theorem freeModuleSheafUnderlyingHomEquiv_triangleBoundary
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (z : (freeModuleSheafFunctor X R).obj (cechEdgeFunctor η) ⟶ F) :
    freeModuleSheafUnderlyingHomEquiv X R (cechTriangleFunctor η) F
        ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
          (freeModuleCechTriangleBoundaryNat R η) ≫ z) =
      (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (freeCechTriangleBoundaryNat η) ≫
          freeModuleSheafUnderlyingHomEquiv X R (cechEdgeFunctor η) F z := by
  rw [freeModuleSheafUnderlyingHomEquiv_eq, Functor.map_comp, ← Category.assoc,
    ← freeModuleSheafIntegerMap_triangleBoundary, Category.assoc,
    ← freeModuleSheafUnderlyingHomEquiv_eq]

/-- Being a cocycle is equivalent for the two actual free sources. -/
theorem freeModuleSheafUnderlyingHomEquiv_cocycle_iff
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (z : (freeModuleSheafFunctor X R).obj (cechEdgeFunctor η) ⟶ F) :
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
        (freeModuleCechTriangleBoundaryNat R η) ≫ z = 0 ↔
      (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (freeCechTriangleBoundaryNat η) ≫
          freeModuleSheafUnderlyingHomEquiv X R (cechEdgeFunctor η) F z = 0 := by
  constructor
  · intro h
    rw [← freeModuleSheafUnderlyingHomEquiv_triangleBoundary, h]
    exact (freeModuleSheafUnderlyingHomAddEquiv X R (cechTriangleFunctor η) F).map_zero
  · intro h
    apply (freeModuleSheafUnderlyingHomEquiv X R (cechTriangleFunctor η) F).injective
    rw [freeModuleSheafUnderlyingHomEquiv_triangleBoundary, h]
    exact (freeModuleSheafUnderlyingHomAddEquiv X R (cechTriangleFunctor η) F).map_zero.symm

end EtaleCohomology
