/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeModuleCechRelations
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Exact free module Cech sheaves

The actual free module augmentation and relation complexes are exact
as presheaves and remain exact after the original sheafification.
These are complexes in the same module-sheaf category used by the
original Yoneda cup product. All coefficient rings, including the
original finite cyclic coefficient rings, are allowed.
-/

@[expose] public section

noncomputable section

universe v u w

open CategoryTheory Limits Opposite

namespace EtaleCohomology

private theorem freeModuleCechEdgeBoundary_freeMk
    (R : Type w) [Ring R] {A B : Type w} (f : A → B) (p : CechEdge f) :
    freeModuleCechEdgeBoundary R f (ModuleCat.freeMk p) =
      ModuleCat.freeMk p.second - ModuleCat.freeMk p.first :=
  ModuleCat.freeDesc_apply (R := R) (M := (ModuleCat.free R).obj A)
    (↾fun p : CechEdge f => ModuleCat.freeMk p.second - ModuleCat.freeMk p.first) p

private theorem freeModuleCechTriangleBoundary_freeMk
    (R : Type w) [Ring R] {A B : Type w} (f : A → B) (t : CechTriangle f) :
    freeModuleCechTriangleBoundary R f (ModuleCat.freeMk t) =
      ModuleCat.freeMk (CechEdge.mk t.second t.third t.same₂) -
        ModuleCat.freeMk (CechEdge.mk t.first t.third (t.same₁.trans t.same₂)) +
      ModuleCat.freeMk (CechEdge.mk t.first t.second t.same₁) :=
  ModuleCat.freeDesc_apply (R := R) (M := (ModuleCat.free R).obj (CechEdge f))
    (↾fun t : CechTriangle f =>
      ModuleCat.freeMk (CechEdge.mk t.second t.third t.same₂) -
        ModuleCat.freeMk (CechEdge.mk t.first t.third (t.same₁.trans t.same₂)) +
      ModuleCat.freeMk (CechEdge.mk t.first t.second t.same₁)) t

variable {C : Type u} [Category.{v} C]
variable (R : Type w) [Ring R] {P Q : C ⥤ Type w} (η : P ⟶ Q)

/-- The actual edge boundary on free module presheaves. -/
def freeModuleCechEdgeBoundaryNat :
    cechEdgeFunctor η ⋙ ModuleCat.free R ⟶ P ⋙ ModuleCat.free R where
  app V := freeModuleCechEdgeBoundary R (η.app V)
  naturality {V W} g := by
    apply ModuleCat.free_hom_ext
    intro p
    change freeModuleCechEdgeBoundary R (η.app W)
        ((ModuleCat.free R).map ((cechEdgeFunctor η).map g) (ModuleCat.freeMk p)) =
      (ModuleCat.free R).map (P.map g)
        (freeModuleCechEdgeBoundary R (η.app V) (ModuleCat.freeMk p))
    let pV : CechEdge (η.app V) := p
    let pW : CechEdge (η.app W) := (cechEdgeFunctor η).map g pV
    let T : (ModuleCat.free R).obj (P.obj V) ⟶
        (ModuleCat.free R).obj (P.obj W) := (ModuleCat.free R).map (P.map g)
    have hV : freeModuleCechEdgeBoundary R (η.app V) (ModuleCat.freeMk pV) =
        ModuleCat.freeMk pV.second - ModuleCat.freeMk pV.first :=
      freeModuleCechEdgeBoundary_freeMk R (η.app V) pV
    have hW : freeModuleCechEdgeBoundary R (η.app W) (ModuleCat.freeMk pW) =
        ModuleCat.freeMk (P.map g pV.second) - ModuleCat.freeMk (P.map g pV.first) :=
      freeModuleCechEdgeBoundary_freeMk R (η.app W) pW
    calc
      _ = freeModuleCechEdgeBoundary R (η.app W) (ModuleCat.freeMk pW) :=
        congrArg (fun c => freeModuleCechEdgeBoundary R (η.app W) c)
          (ModuleCat.free_map_apply (R := R) ((cechEdgeFunctor η).map g) pV)
      _ = ModuleCat.freeMk (P.map g pV.second) -
          ModuleCat.freeMk (P.map g pV.first) := hW
      _ = T (ModuleCat.freeMk pV.second) - T (ModuleCat.freeMk pV.first) :=
        congrArg₂ (fun (x y : (ModuleCat.free R).obj (P.obj W)) => x - y)
          (ModuleCat.free_map_apply (R := R) (P.map g) pV.second).symm
          (ModuleCat.free_map_apply (R := R) (P.map g) pV.first).symm
      _ = T (ModuleCat.freeMk pV.second - ModuleCat.freeMk pV.first) :=
        (map_sub T.hom (ModuleCat.freeMk pV.second) (ModuleCat.freeMk pV.first)).symm
      _ = T (freeModuleCechEdgeBoundary R (η.app V) (ModuleCat.freeMk pV)) :=
        congrArg (fun c => T c) hV.symm

/-- The actual triangle boundary on free module presheaves. -/
def freeModuleCechTriangleBoundaryNat :
    cechTriangleFunctor η ⋙ ModuleCat.free R ⟶
      cechEdgeFunctor η ⋙ ModuleCat.free R where
  app V := freeModuleCechTriangleBoundary R (η.app V)
  naturality {V W} g := by
    apply ModuleCat.free_hom_ext
    intro t
    change freeModuleCechTriangleBoundary R (η.app W)
        ((ModuleCat.free R).map ((cechTriangleFunctor η).map g) (ModuleCat.freeMk t)) =
      (ModuleCat.free R).map ((cechEdgeFunctor η).map g)
        (freeModuleCechTriangleBoundary R (η.app V) (ModuleCat.freeMk t))
    let tV : CechTriangle (η.app V) := t
    let tW : CechTriangle (η.app W) := (cechTriangleFunctor η).map g tV
    let e₂₃ : CechEdge (η.app V) := CechEdge.mk tV.second tV.third tV.same₂
    let e₁₃ : CechEdge (η.app V) :=
      CechEdge.mk tV.first tV.third (tV.same₁.trans tV.same₂)
    let e₁₂ : CechEdge (η.app V) := CechEdge.mk tV.first tV.second tV.same₁
    let m : CechEdge (η.app V) ⟶ CechEdge (η.app W) := (cechEdgeFunctor η).map g
    let T : (ModuleCat.free R).obj (CechEdge (η.app V)) ⟶
        (ModuleCat.free R).obj (CechEdge (η.app W)) := (ModuleCat.free R).map m
    have hV : freeModuleCechTriangleBoundary R (η.app V) (ModuleCat.freeMk tV) =
        ModuleCat.freeMk e₂₃ - ModuleCat.freeMk e₁₃ + ModuleCat.freeMk e₁₂ :=
      freeModuleCechTriangleBoundary_freeMk R (η.app V) tV
    have hW : freeModuleCechTriangleBoundary R (η.app W) (ModuleCat.freeMk tW) =
        ModuleCat.freeMk (m e₂₃) - ModuleCat.freeMk (m e₁₃) +
          ModuleCat.freeMk (m e₁₂) :=
      freeModuleCechTriangleBoundary_freeMk R (η.app W) tW
    calc
      _ = freeModuleCechTriangleBoundary R (η.app W) (ModuleCat.freeMk tW) :=
        congrArg (fun c => freeModuleCechTriangleBoundary R (η.app W) c)
          (ModuleCat.free_map_apply (R := R) ((cechTriangleFunctor η).map g) tV)
      _ = ModuleCat.freeMk (m e₂₃) - ModuleCat.freeMk (m e₁₃) +
          ModuleCat.freeMk (m e₁₂) := hW
      _ = T (ModuleCat.freeMk e₂₃) - T (ModuleCat.freeMk e₁₃) +
          T (ModuleCat.freeMk e₁₂) :=
        congrArg₂
          (fun (x y : (ModuleCat.free R).obj (CechEdge (η.app W))) => x + y)
          (congrArg₂
            (fun (x y : (ModuleCat.free R).obj (CechEdge (η.app W))) => x - y)
            (ModuleCat.free_map_apply (R := R) m e₂₃).symm
            (ModuleCat.free_map_apply (R := R) m e₁₃).symm)
          (ModuleCat.free_map_apply (R := R) m e₁₂).symm
      _ = T (ModuleCat.freeMk e₂₃ - ModuleCat.freeMk e₁₃) +
          T (ModuleCat.freeMk e₁₂) :=
        congrArg (fun c => c + T (ModuleCat.freeMk e₁₂))
          (map_sub T.hom (ModuleCat.freeMk e₂₃) (ModuleCat.freeMk e₁₃)).symm
      _ = T (ModuleCat.freeMk e₂₃ - ModuleCat.freeMk e₁₃ + ModuleCat.freeMk e₁₂) :=
        (map_add T.hom (ModuleCat.freeMk e₂₃ - ModuleCat.freeMk e₁₃)
          (ModuleCat.freeMk e₁₂)).symm
      _ = T (freeModuleCechTriangleBoundary R (η.app V) (ModuleCat.freeMk tV)) :=
        congrArg (fun c => T c) hV.symm

/-- The native free-module complex of first Cech relations. -/
def freeModuleCechRelationComplex : ShortComplex (C ⥤ ModuleCat.{w} R) :=
  ShortComplex.mk (freeModuleCechTriangleBoundaryNat R η)
    (freeModuleCechEdgeBoundaryNat R η) (by
      apply NatTrans.ext
      funext V
      exact freeModuleCechTriangle_boundary R (η.app V))

/-- Exactness follows pointwise from the explicit contraction of
the original free module edge and triangle objects. -/
theorem freeModuleCechRelationComplex_exact :
    (freeModuleCechRelationComplex R η).Exact := by
  let S := freeModuleCechRelationComplex R η
  have hV (V : C) : (S.map ((evaluation C (ModuleCat.{w} R)).obj V)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro c hc
    exact exists_freeModuleCechTriangle_primitive R (η.app V) c hc
  rw [S.exact_iff_iCycles_pOpcycles_zero]
  apply NatTrans.ext
  funext V
  exact (hV V).comp_eq_zero
    (congrArg (fun k => k.app V) S.iCycles_g)
    (congrArg (fun k => k.app V) S.f_pOpcycles)

/-- The native free-module augmentation complex. -/
def freeModuleCechAugmentationComplex : ShortComplex (C ⥤ ModuleCat.{w} R) :=
  ShortComplex.mk (freeModuleCechEdgeBoundaryNat R η)
    (Functor.whiskerRight η (ModuleCat.free R)) (by
      apply NatTrans.ext
      funext V
      exact freeModuleCechEdge_augmentation R (η.app V))

/-- The original edge boundaries generate exactly the augmentation
kernel as a presheaf of modules. -/
theorem freeModuleCechAugmentationComplex_exact :
    (freeModuleCechAugmentationComplex R η).Exact := by
  let S := freeModuleCechAugmentationComplex R η
  have hV (V : C) : (S.map ((evaluation C (ModuleCat.{w} R)).obj V)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro c hc
    exact exists_freeModuleCechEdge_primitive R (η.app V) c hc
  rw [S.exact_iff_iCycles_pOpcycles_zero]
  apply NatTrans.ext
  funext V
  exact (hV V).comp_eq_zero
    (congrArg (fun k => k.app V) S.iCycles_g)
    (congrArg (fun k => k.app V) S.f_pOpcycles)

variable {D : Type u} [Category.{v} D] (J : GrothendieckTopology D)
  [HasSheafify J (ModuleCat.{w} R)]
  {P' Q' : Dᵒᵖ ⥤ Type w} (ρ : P' ⟶ Q')

/-- The native module-sheaf relation complex is exact. -/
theorem freeModuleCechRelationComplex_sheaf_exact :
    ((freeModuleCechRelationComplex R ρ).map
      (presheafToSheaf J (ModuleCat.{w} R))).Exact :=
  (freeModuleCechRelationComplex_exact R ρ).map _

/-- The native module-sheaf augmentation complex is exact. -/
theorem freeModuleCechAugmentationComplex_sheaf_exact :
    ((freeModuleCechAugmentationComplex R ρ).map
      (presheafToSheaf J (ModuleCat.{w} R))).Exact :=
  (freeModuleCechAugmentationComplex_exact R ρ).map _

end EtaleCohomology
