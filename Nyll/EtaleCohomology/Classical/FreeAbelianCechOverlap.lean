/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRelations
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Whiskering

/-!
# The actual self-overlap in the abelian Cech resolution

The free edge sheaf is the original free representable of the actual
self-overlap. Under this isomorphism its boundary is the second
projection minus the first. Consequently a class restricted through
the first covering kernel has precisely this difference of its two
original overlap restrictions.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

/-- Original Čech edges identify with morphisms into the self-overlap. -/
def cechEdgeYonedaEquiv
    {C : Type u} [Category.{v} C] {V W : C} (f : V ⟶ W)
    [HasPullback f f] (T : C) :
    CechEdge ((yoneda.map f).app (op T)) ≃ (T ⟶ pullback f f) where
  toFun p := pullback.lift p.first p.second p.same
  invFun a := ⟨a ≫ pullback.fst f f, a ≫ pullback.snd f f, by
    change (a ≫ pullback.fst f f) ≫ f = (a ≫ pullback.snd f f) ≫ f
    rw [Category.assoc, Category.assoc, pullback.condition]⟩
  left_inv p := by
    apply CechEdge.ext
    · exact pullback.lift_fst p.first p.second p.same
    · exact pullback.lift_snd p.first p.second p.same
  right_inv a := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _

/-- The Čech edge presheaf is represented by the original self-overlap. -/
def cechEdgeYonedaIso
    {C : Type u} [Category.{v} C] {V W : C} (f : V ⟶ W)
    [HasPullback f f] : cechEdgeFunctor (yoneda.map f) ≅ yoneda.obj (pullback f f) :=
  NatIso.ofComponents (fun T => (cechEdgeYonedaEquiv f T.unop).toIso) (by
    intro T T' a
    ext p₀
    let p : CechEdge ((yoneda.map f).app (op T.unop)) := p₀
    change pullback.lift (a.unop ≫ p.first) (a.unop ≫ p.second) _ =
      a.unop ≫ pullback.lift p.first p.second p.same
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans
        ((Category.assoc a.unop (pullback.lift p.first p.second p.same)
          (pullback.fst f f)).trans
            (congrArg (fun b => a.unop ≫ b)
              (pullback.lift_fst p.first p.second p.same))).symm
    · exact (pullback.lift_snd _ _ _).trans
        ((Category.assoc a.unop (pullback.lift p.first p.second p.same)
          (pullback.snd f f)).trans
            (congrArg (fun b => a.unop ≫ b)
              (pullback.lift_snd p.first p.second p.same))).symm)

/-- The original free edge sheaf is the original free representable
of the actual categorical self-overlap. -/
def freeCechEdgeSheafIso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] {V W : C} (f : V ⟶ W)
    [HasPullback f f] :
    (presheafToSheaf J AddCommGrpCat.{v}).obj
        (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free) ≅
      (freeAbelianSheafYoneda J).obj (pullback f f) :=
  (presheafToSheaf J AddCommGrpCat.{v}).mapIso
    (Functor.isoWhiskerRight (cechEdgeYonedaIso f) AddCommGrpCat.free)

private theorem cechEdgeYonedaIso_boundary
    {C : Type u} [Category.{v} C] {V W : C} (f : V ⟶ W) [HasPullback f f] :
    (Functor.isoWhiskerRight (cechEdgeYonedaIso f) AddCommGrpCat.free).inv ≫
        freeCechEdgeBoundaryNat (yoneda.map f) =
      Functor.whiskerRight (yoneda.map (pullback.snd f f)) AddCommGrpCat.free -
        Functor.whiskerRight (yoneda.map (pullback.fst f f)) AddCommGrpCat.free := by
  apply NatTrans.ext
  funext T
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro a
  change freeCechEdgeBoundary ((yoneda.map f).app T)
      (FreeAbelianGroup.map ((cechEdgeYonedaEquiv f T.unop).symm)
        (FreeAbelianGroup.of a)) =
    FreeAbelianGroup.map (fun b => b ≫ pullback.snd f f) (FreeAbelianGroup.of a) -
      FreeAbelianGroup.map (fun b => b ≫ pullback.fst f f) (FreeAbelianGroup.of a)
  simp only [FreeAbelianGroup.map_of_apply, freeCechEdgeBoundary,
    FreeAbelianGroup.lift_apply_of]
  rfl

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] {V T : C} (f : V ⟶ T) [HasPullback f f]

/-- On the original self-overlap, the original edge boundary is
the second projection minus the first projection. -/
theorem freeCechEdgeSheafIso_boundary :
    (freeCechEdgeSheafIso J f).inv ≫
        (presheafToSheaf J AddCommGrpCat.{v}).map (freeCechEdgeBoundaryNat (yoneda.map f)) =
      (freeAbelianSheafYoneda J).map (pullback.snd f f) -
        (freeAbelianSheafYoneda J).map (pullback.fst f f) := by
  change (presheafToSheaf J AddCommGrpCat.{v}).map
      (Functor.isoWhiskerRight (cechEdgeYonedaIso f) AddCommGrpCat.free).inv ≫
    (presheafToSheaf J AddCommGrpCat.{v}).map (freeCechEdgeBoundaryNat (yoneda.map f)) = _
  rw [← Functor.map_comp, cechEdgeYonedaIso_boundary, Functor.map_sub]
  rfl

/-- Restriction through the first covering kernel is exactly the
difference of the two original overlap restrictions, in every degree. -/
theorem abelianCechFirstRelation_overlap_restriction
    [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] (hT : IsTerminal T)
    (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (β : Sheaf.H'.{v} F n V) :
    (Ext.mk₀ ((freeCechEdgeSheafIso J f).inv ≫
      abelianCechFirstRelationMap J hT f)).comp
        ((Ext.mk₀ (kernel.ι (abelianCechUnitAugmentation J hT f))).comp β (zero_add n))
          (zero_add n) =
      (F.cohomologyPresheaf n).map (pullback.snd f f).op β -
        (F.cohomologyPresheaf n).map (pullback.fst f f).op β := by
  let β₀ : Ext ((freeAbelianSheafYoneda J).obj V) F n := β
  change (Ext.mk₀ ((freeCechEdgeSheafIso J f).inv ≫
    abelianCechFirstRelationMap J hT f)).comp
      ((Ext.mk₀ (kernel.ι (abelianCechUnitAugmentation J hT f))).comp β₀ (zero_add n))
        (zero_add n) =
    (Ext.mk₀ ((freeAbelianSheafYoneda J).map (pullback.snd f f))).comp β₀ (zero_add n) -
      (Ext.mk₀ ((freeAbelianSheafYoneda J).map (pullback.fst f f))).comp β₀ (zero_add n)
  rw [Ext.mk₀_comp_mk₀_assoc, Category.assoc,
    abelianCechFirstRelationMap_comp, freeCechEdgeSheafIso_boundary]
  simp only [sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg, Ext.add_comp, Ext.neg_comp]

end EtaleCohomology
