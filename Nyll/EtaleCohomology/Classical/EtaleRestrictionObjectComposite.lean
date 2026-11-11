/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectComparison
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectLocalization
public import Nyll.EtaleCohomology.Classical.AbelianRestrictionPullback
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionCohomologyComparison
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# EtaleRestrictionObjectComposite

The actual source-evaluation law for composed restriction on Ext.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable {X : Scheme.{u}} {V W : X.Etale} (g : W ⟶ V)

/-- The actual composed restriction is the exact-functor map preceded by its original source. -/
theorem etaleRestrictionObject_composite_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (a : Sheaf.H'.{u} F n V) :
    Sheaf.H.map ((etaleRestrictionObjectIso g).hom.app F) n
        (etaleAbelianRestrictionCohomologyPullback g.left
          ((etaleRestriction V.hom AddCommGrpCat.{u}).obj F) n
            (etaleCohomologyPresheafRestrictionEquiv V F n a)) =
      (Ext.mk₀ (etaleRestrictionPullbackSource (Scheme.Etale.mk g.left) ≫
        (etaleRestriction g.left AddCommGrpCat.{u}).map (etaleRestrictionObjectSource V) ≫
          (etaleRestrictionObjectIso g).hom.app
            ((freeAbelianSheafYoneda X.smallEtaleTopology).obj V))).comp
        (a.mapExactFunctor (etaleRestriction W.hom AddCommGrpCat.{u})) (zero_add n) := by
  let A := (constantSheaf V.left.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let B := (constantSheaf W.left.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let P := (freeAbelianSheafYoneda X.smallEtaleTopology).obj V
  let D := etaleRestriction V.hom AddCommGrpCat.{u}
  let R := etaleRestriction g.left AddCommGrpCat.{u}
  let T := etaleRestriction W.hom AddCommGrpCat.{u}
  let I : D ⋙ R ⟶ T := (etaleRestrictionObjectIso g).hom
  let s : B ⟶ R.obj A := etaleRestrictionPullbackSource (Scheme.Etale.mk g.left)
  let t : A ⟶ D.obj P := etaleRestrictionObjectSource V
  let j : B ⟶ R.obj (D.obj P) := s ≫ R.map t
  have hmap : (etaleCohomologyPresheafRestrictionEquiv V F n a).mapExactFunctor R =
      (Ext.mk₀ (R.map t)).comp
        ((a.mapExactFunctor D).mapExactFunctor R) (zero_add n) :=
    (congrArg (fun z : Ext.{u} A (D.obj F) n => z.mapExactFunctor R)
      (etaleCohomologyPresheafRestrictionEquiv_apply V F n a)).trans
        ((Ext.mapExactFunctor_comp R (Ext.mk₀ t) (a.mapExactFunctor D)
          (zero_add n)).trans
            (congrArg (fun z : Ext.{u} (R.obj A) (R.obj (D.obj P)) 0 =>
              z.comp ((a.mapExactFunctor D).mapExactFunctor R) (zero_add n))
                (Ext.mapExactFunctor_mk₀ R t)))
  have hsource : (Ext.mk₀ s).comp
      ((etaleCohomologyPresheafRestrictionEquiv V F n a).mapExactFunctor R)
        (zero_add n) =
      (Ext.mk₀ j).comp ((a.mapExactFunctor D).mapExactFunctor R) (zero_add n) :=
    (congrArg (fun z : Ext.{u} (R.obj A) (R.obj (D.obj F)) n =>
      (Ext.mk₀ s).comp z (zero_add n)) hmap).trans
        (Ext.mk₀_comp_mk₀_assoc s (R.map t) ((a.mapExactFunctor D).mapExactFunctor R))
  have hnatural : ((a.mapExactFunctor D).mapExactFunctor R).comp
      (Ext.mk₀ (I.app F)) (add_zero n) =
      (Ext.mk₀ (I.app P)).comp (a.mapExactFunctor T) (zero_add n) :=
    (congrArg (fun z : Ext.{u} (R.obj (D.obj P)) (R.obj (D.obj F)) n =>
      z.comp (Ext.mk₀ (I.app F)) (add_zero n))
        (Ext.comp_mapExactFunctor a D R).symm).trans
          (Ext.mapExactFunctor_comp_mk₀_natTransApp a I)
  have hcomp : ((Ext.mk₀ j).comp ((a.mapExactFunctor D).mapExactFunctor R)
      (zero_add n)).comp (Ext.mk₀ (I.app F)) (add_zero n) =
      (Ext.mk₀ (s ≫ R.map t ≫ I.app P)).comp (a.mapExactFunctor T) (zero_add n) :=
    (Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ j)
      ((a.mapExactFunctor D).mapExactFunctor R) (Ext.mk₀ (I.app F)) (zero_add n)).trans
        ((congrArg (fun z : Ext.{u} (R.obj (D.obj P)) (T.obj F) n =>
          (Ext.mk₀ j).comp z (zero_add n)) hnatural).trans
            ((Ext.mk₀_comp_mk₀_assoc j (I.app P) (a.mapExactFunctor T)).trans
              (congrArg (fun k : B ⟶ T.obj P =>
                (Ext.mk₀ k).comp (a.mapExactFunctor T) (zero_add n))
                  (Category.assoc s (R.map t) (I.app P)))))
  have hpb := etaleRestrictionPullbackSource_apply (Scheme.Etale.mk g.left)
    ((etaleRestriction V.hom AddCommGrpCat.{u}).obj F) n
      (etaleCohomologyPresheafRestrictionEquiv V F n a)
  refine (congrArg (Sheaf.H.map ((etaleRestrictionObjectIso g).hom.app F) n) hpb).trans ?_
  change ((Ext.mk₀ s).comp
    ((etaleCohomologyPresheafRestrictionEquiv V F n a).mapExactFunctor R)
      (zero_add n)).comp (Ext.mk₀ (I.app F)) (add_zero n) = _
  exact (congrArg (fun z : Ext.{u} B (R.obj (D.obj F)) n =>
    z.comp (Ext.mk₀ (I.app F)) (add_zero n)) hsource).trans hcomp

end EtaleCohomology
