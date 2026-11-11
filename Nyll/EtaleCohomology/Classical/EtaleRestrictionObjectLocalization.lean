/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionCohomologySections
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionNaturality
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleSlice
public import Nyll.SchemeTheory.Sheaves.OverExtension
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# EtaleRestrictionObjectLocalization

The actual source morphism for localization and its unchanged all-degree Ext formula.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable {X : Scheme.{u}} {V W : X.Etale} (g : W ⟶ V)

variable (V) in
/-- The original source morphism of localization at an étale object,
before composing with any particular cohomology class. -/
def etaleRestrictionObjectSource :
    (constantSheaf V.left.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      (etaleRestriction V.hom AddCommGrpCat.{u}).obj
        ((freeAbelianSheafYoneda X.smallEtaleTopology).obj V) :=
  ((etaleSliceAbelianConstantIso V).app (AddCommGrpCat.of (ULift.{u} ℤ))).inv ≫
    (etaleSliceAbelianSheafEquivalence V).functor.map
      ((overAbelianSheafExtensionAdjunction V X.smallEtaleTopology).homEquiv _ _
        (freeAbelianSheafYonedaOverExtensionIso X.smallEtaleTopology V).inv)

variable (V) in
/-- Localization is the original exact-functor map on Ext, preceded
by the original source morphism on the free representable. -/
theorem etaleCohomologyPresheafRestrictionEquiv_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (a : Sheaf.H'.{u} F n V) :
    etaleCohomologyPresheafRestrictionEquiv V F n a =
      (Ext.mk₀ (etaleRestrictionObjectSource V)).comp
        (a.mapExactFunctor (etaleRestriction V.hom AddCommGrpCat.{u})) (zero_add n) := by
  let A := AddCommGrpCat.of (ULift.{u} ℤ)
  let P := (freeAbelianSheafYoneda X.smallEtaleTopology).obj V
  let ZO := (constantSheaf (X.smallEtaleTopology.over V) AddCommGrpCat.{u}).obj A
  let D := X.smallEtaleTopology.overPullback AddCommGrpCat.{u} V
  let E := etaleSliceAbelianSheafEquivalence V
  let adj := overAbelianSheafExtensionAdjunction V X.smallEtaleTopology
  let j : (overAbelianSheafExtension V X.smallEtaleTopology).obj ZO ⟶ P :=
    (freeAbelianSheafYonedaOverExtensionIso X.smallEtaleTopology V).inv
  let r : ZO ⟶ D.obj P := adj.homEquiv ZO P j
  let e : E.functor.obj ZO ≅
      (constantSheaf V.left.smallEtaleTopology AddCommGrpCat.{u}).obj A :=
    (etaleSliceAbelianConstantIso V).app A
  let b : Ext.{u} ZO (D.obj F) n := (Ext.mk₀ r).comp (a.mapExactFunctor D) (zero_add n)
  have hq : adj.extEquiv ((Ext.mk₀ j).comp a (zero_add n)) = b :=
    (adj.extEquiv_naturality_right (Ext.mk₀ j) a (zero_add n)).trans
      (congrArg (fun z : Ext.{u} ZO (D.obj P) 0 =>
        z.comp (a.mapExactFunctor D) (zero_add n)) (adj.extEquiv_mk₀ j))
  have hbmap : b.mapExactFunctor E.functor =
      (Ext.mk₀ (E.functor.map r)).comp
        ((a.mapExactFunctor D).mapExactFunctor E.functor) (zero_add n) :=
    (Ext.mapExactFunctor_comp E.functor (Ext.mk₀ r)
      (a.mapExactFunctor D) (zero_add n)).trans
      (congrArg (fun z : Ext.{u} (E.functor.obj ZO) (E.functor.obj (D.obj P)) 0 =>
        z.comp ((a.mapExactFunctor D).mapExactFunctor E.functor) (zero_add n))
          (Ext.mapExactFunctor_mk₀ E.functor r))
  have hmap : (a.mapExactFunctor D).mapExactFunctor E.functor =
      a.mapExactFunctor (etaleRestriction V.hom AddCommGrpCat.{u}) :=
    (Ext.comp_mapExactFunctor a D E.functor).symm
  have hover : etaleCohomologyPresheafRestrictionEquiv V F n a =
      etaleSliceAbelianCohomologyEquiv V (D.obj F) n
        (adj.extEquiv ((Ext.mk₀ j).comp a (zero_add n))) := rfl
  exact hover.trans
    ((congrArg (etaleSliceAbelianCohomologyEquiv V (D.obj F) n) hq).trans
      ((etaleSliceAbelianCohomologyEquiv_apply V (D.obj F) n b).trans
        ((congrArg (fun z : Ext.{u} (E.functor.obj ZO) (E.functor.obj (D.obj F)) n =>
          (Ext.mk₀ e.inv).comp z (zero_add n)) hbmap).trans
          ((Ext.mk₀_comp_mk₀_assoc e.inv (E.functor.map r)
            ((a.mapExactFunctor D).mapExactFunctor E.functor)).trans
            (congrArg (fun z : Ext.{u}
                ((etaleRestriction V.hom AddCommGrpCat.{u}).obj P)
                ((etaleRestriction V.hom AddCommGrpCat.{u}).obj F) n =>
              (Ext.mk₀ (etaleRestrictionObjectSource V)).comp z (zero_add n)) hmap)))))

end EtaleCohomology
