/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeModuleCechFaces
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCoalgebra
public import Mathlib.Tactic.Abel

/-!
# The actual Cech cup calculation on triangles

For an actual coefficient-valued edge cocycle `a`, multiplying its
value on an edge by a lift at the first endpoint gives a relation
lift. Its boundary on `012` is the action of `a₁₂` on `b₁ - b₀`.
All maps are the original free module sheaf maps and the original
tensor-unit action. The order follows the native Yoneda convention.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped EtaleCohomology.ModuleTensor

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]
  {P Q : X.Etaleᵒᵖ ⥤ Type u} (η : P ⟶ Q)

/-- The original alternating cocycle equation determines the long
edge as the sum of the two consecutive edges. -/
theorem freeModuleCechCocycle_longEdge
    {E : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (a : (freeModuleSheafFunctor X R).obj (cechEdgeFunctor η) ⟶ E)
    (ha : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
      (freeModuleCechTriangleBoundaryNat R η) ≫ a = 0) :
    (freeModuleSheafFunctor X R).map (cechTriangleEdge02 η) ≫ a =
      (freeModuleSheafFunctor X R).map (cechTriangleEdge12 η) ≫ a +
        (freeModuleSheafFunctor X R).map (cechTriangleEdge01 η) ≫ a := by
  rw [freeModuleCechTriangleBoundarySheaf_faces,
    Preadditive.add_comp, Preadditive.sub_comp] at ha
  let a₁₂ := (freeModuleSheafFunctor X R).map (cechTriangleEdge12 η) ≫ a
  let a₀₂ := (freeModuleSheafFunctor X R).map (cechTriangleEdge02 η) ≫ a
  let a₀₁ := (freeModuleSheafFunctor X R).map (cechTriangleEdge01 η) ≫ a
  change a₁₂ - a₀₂ + a₀₁ = 0 at ha
  change a₀₂ = a₁₂ + a₀₁
  have h := congrArg (fun z => z + a₀₂) ha
  have hsum : (a₁₂ - a₀₂ + a₀₁) + a₀₂ = a₁₂ + a₀₁ := by abel
  rw [hsum, zero_add] at h
  exact h.symm

/-- The native triangle boundary of the actual first-endpoint lift
is `a₁₂` acting on the original difference along edge `01`. -/
theorem freeModuleCechAction_triangle
    {E : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (a : (freeModuleSheafFunctor X R).obj (cechEdgeFunctor η) ⟶
      𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)))
    (ha : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
      (freeModuleCechTriangleBoundaryNat R η) ≫ a = 0)
    (b : (freeModuleSheafFunctor X R).obj P ⟶ E) :
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
        (freeModuleCechTriangleBoundaryNat R η) ≫
      freeModuleSheafAction X R a
        ((freeModuleSheafFunctor X R).map (cechEdgeFirst η) ≫ b) =
      freeModuleSheafAction X R
        ((freeModuleSheafFunctor X R).map (cechTriangleEdge12 η) ≫ a)
        ((freeModuleSheafFunctor X R).map (cechTriangleEdge01 η) ≫
          (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
            (freeModuleCechEdgeBoundaryNat R η) ≫ b) := by
  let F := freeModuleSheafFunctor X R
  let a₁₂ := F.map (cechTriangleEdge12 η) ≫ a
  let a₀₂ := F.map (cechTriangleEdge02 η) ≫ a
  let a₀₁ := F.map (cechTriangleEdge01 η) ≫ a
  let b₀ := F.map (cechTriangleEdge01 η) ≫ F.map (cechEdgeFirst η) ≫ b
  let b₁ := F.map (cechTriangleEdge01 η) ≫ F.map (cechEdgeSecond η) ≫ b
  have h₀₂ : a₀₂ = a₁₂ + a₀₁ := freeModuleCechCocycle_longEdge X R η a ha
  have hface₁₂ : F.map (cechTriangleEdge12 η) ≫
      (F.map (cechEdgeFirst η) ≫ b) = b₁ := by
    change F.map (cechTriangleEdge12 η) ≫ (F.map (cechEdgeFirst η) ≫ b) =
      F.map (cechTriangleEdge01 η) ≫ (F.map (cechEdgeSecond η) ≫ b)
    rw [← Category.assoc, ← Functor.map_comp, cechTriangleEdge12_first,
      Functor.map_comp, Category.assoc]
  have hface₀₂ : F.map (cechTriangleEdge02 η) ≫
      (F.map (cechEdgeFirst η) ≫ b) = b₀ := by
    change F.map (cechTriangleEdge02 η) ≫ (F.map (cechEdgeFirst η) ≫ b) =
      F.map (cechTriangleEdge01 η) ≫ (F.map (cechEdgeFirst η) ≫ b)
    rw [← Category.assoc, ← Functor.map_comp, cechTriangleEdge02_first,
      Functor.map_comp, Category.assoc]
  have hdiff : b₁ - b₀ = F.map (cechTriangleEdge01 η) ≫
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
        (freeModuleCechEdgeBoundaryNat R η) ≫ b := by
    rw [freeModuleCechEdgeBoundarySheaf_faces,
      Preadditive.sub_comp, Preadditive.comp_sub]
    rfl
  calc
    _ = freeModuleSheafAction X R a₁₂ b₁ -
        freeModuleSheafAction X R a₀₂ b₀ + freeModuleSheafAction X R a₀₁ b₀ := by
      rw [freeModuleCechTriangleBoundarySheaf_faces,
        Preadditive.add_comp, Preadditive.sub_comp]
      change F.map (cechTriangleEdge12 η) ≫ freeModuleSheafAction X R a
          (F.map (cechEdgeFirst η) ≫ b) -
        F.map (cechTriangleEdge02 η) ≫ freeModuleSheafAction X R a
          (F.map (cechEdgeFirst η) ≫ b) +
        F.map (cechTriangleEdge01 η) ≫ freeModuleSheafAction X R a
          (F.map (cechEdgeFirst η) ≫ b) = _
      rw [freeModuleSheafAction_precomp, freeModuleSheafAction_precomp,
        freeModuleSheafAction_precomp, hface₁₂, hface₀₂]
    _ = freeModuleSheafAction X R a₁₂ (b₁ - b₀) := by
      rw [h₀₂, freeModuleSheafAction_add_left, freeModuleSheafAction_sub_right]
      abel
    _ = _ := congrArg (freeModuleSheafAction X R a₁₂) hdiff

end EtaleCohomology
