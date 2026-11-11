/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectComparison
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectLocalization
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectSections
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectComposite
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# EtaleRestrictionObjectCohomology

The original all-degree object restriction through its original source equality.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable {X : Scheme.{u}} {V W : X.Etale} (g : W ⟶ V)

/-- Restriction in the original cohomology presheaf agrees with the
original scheme pullback for every morphism of étale objects and
every degree. No descent of the class to the base is required. -/
theorem etaleCohomologyPresheafRestrictionEquiv_object_restriction
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (a : Sheaf.H'.{u} F n V) :
    etaleCohomologyPresheafRestrictionEquiv W F n
        ((F.cohomologyPresheaf n).map g.op a) =
      Sheaf.H.map ((etaleRestrictionObjectIso g).hom.app F) n
        (etaleAbelianRestrictionCohomologyPullback g.left
          ((etaleRestriction V.hom AddCommGrpCat.{u}).obj F) n
            (etaleCohomologyPresheafRestrictionEquiv V F n a)) := by
  let P := (freeAbelianSheafYoneda X.smallEtaleTopology).obj V
  have hs : etaleRestrictionObjectSource W ≫
        (etaleRestriction W.hom AddCommGrpCat.{u}).map
          ((freeAbelianSheafYoneda X.smallEtaleTopology).map g) =
      etaleRestrictionPullbackSource (Scheme.Etale.mk g.left) ≫
        (etaleRestriction g.left AddCommGrpCat.{u}).map (etaleRestrictionObjectSource V) ≫
          (etaleRestrictionObjectIso g).hom.app P := by
    apply (Ext.mk₀_bijective _ ((etaleRestriction W.hom AddCommGrpCat.{u}).obj P)).injective
    have hzero := etaleCohomologyPresheafRestrictionEquiv_object_restriction_zero
      g P (Ext.mk₀ (𝟙 P))
    have hleft := etaleCohomologyPresheafRestrictionEquiv_apply W P 0
      ((P.cohomologyPresheaf 0).map g.op (Ext.mk₀ (𝟙 P)))
    have hright := etaleRestrictionObject_composite_apply g P 0 (Ext.mk₀ (𝟙 P))
    have h := hleft.symm.trans (hzero.trans hright)
    change (Ext.mk₀ (etaleRestrictionObjectSource W)).comp
      (((Ext.mk₀ ((freeAbelianSheafYoneda X.smallEtaleTopology).map g)).comp
        (Ext.mk₀ (𝟙 P)) (zero_add 0)).mapExactFunctor
          (etaleRestriction W.hom AddCommGrpCat.{u})) (zero_add 0) = _ at h
    let R := etaleRestriction W.hom AddCommGrpCat.{u}
    let m := (freeAbelianSheafYoneda X.smallEtaleTopology).map g
    let p := etaleRestrictionObjectSource W
    let q := etaleRestrictionPullbackSource (Scheme.Etale.mk g.left) ≫
      (etaleRestriction g.left AddCommGrpCat.{u}).map (etaleRestrictionObjectSource V) ≫
        (etaleRestrictionObjectIso g).hom.app P
    have hm : ((Ext.mk₀ m).comp (Ext.mk₀ (𝟙 P)) (zero_add 0)).mapExactFunctor R =
        Ext.mk₀ (R.map m) :=
      (congrArg (fun z : Ext.{u}
          ((freeAbelianSheafYoneda X.smallEtaleTopology).obj W) P 0 =>
        z.mapExactFunctor R) (Ext.comp_mk₀_id (Ext.mk₀ m))).trans
          (Ext.mapExactFunctor_mk₀ R m)
    have hid : (Ext.mk₀ (𝟙 P)).mapExactFunctor R = Ext.mk₀ (𝟙 (R.obj P)) :=
      (Ext.mapExactFunctor_mk₀ R (𝟙 P)).trans
        (congrArg (fun k : R.obj P ⟶ R.obj P => Ext.mk₀ k) (R.map_id P))
    have hp : (Ext.mk₀ p).comp
        (((Ext.mk₀ m).comp (Ext.mk₀ (𝟙 P)) (zero_add 0)).mapExactFunctor R)
          (zero_add 0) = Ext.mk₀ (p ≫ R.map m) :=
      (congrArg (fun z : Ext.{u}
          (R.obj ((freeAbelianSheafYoneda X.smallEtaleTopology).obj W)) (R.obj P) 0 =>
        (Ext.mk₀ p).comp z (zero_add 0)) hm).trans (Ext.mk₀_comp_mk₀ p (R.map m))
    have hq : (Ext.mk₀ q).comp ((Ext.mk₀ (𝟙 P)).mapExactFunctor R) (zero_add 0) =
        Ext.mk₀ q :=
      (congrArg (fun z : Ext.{u} (R.obj P) (R.obj P) 0 =>
        (Ext.mk₀ q).comp z (zero_add 0)) hid).trans (Ext.comp_mk₀_id (Ext.mk₀ q))
    exact hp.symm.trans (h.trans hq)
  have hleft := etaleCohomologyPresheafRestrictionEquiv_apply W F n
    ((F.cohomologyPresheaf n).map g.op a)
  have hright := etaleRestrictionObject_composite_apply g F n a
  let R := etaleRestriction W.hom AddCommGrpCat.{u}
  let m := (freeAbelianSheafYoneda X.smallEtaleTopology).map g
  let s := etaleRestrictionObjectSource W
  let q := etaleRestrictionPullbackSource (Scheme.Etale.mk g.left) ≫
    (etaleRestriction g.left AddCommGrpCat.{u}).map (etaleRestrictionObjectSource V) ≫
      (etaleRestrictionObjectIso g).hom.app P
  have hmap := Ext.mapExactFunctor_comp R (Ext.mk₀ m) a (zero_add n)
  have hmk := Ext.mapExactFunctor_mk₀ R m
  have hstep : (Ext.mk₀ s).comp
      (((Ext.mk₀ m).comp a (zero_add n)).mapExactFunctor R) (zero_add n) =
      (Ext.mk₀ q).comp (a.mapExactFunctor R) (zero_add n) :=
    (congrArg (fun z : Ext.{u}
        (R.obj ((freeAbelianSheafYoneda X.smallEtaleTopology).obj W)) (R.obj F) n =>
      (Ext.mk₀ s).comp z (zero_add n)) hmap).trans
        ((congrArg (fun z : Ext.{u}
            (R.obj ((freeAbelianSheafYoneda X.smallEtaleTopology).obj W)) (R.obj P) 0 =>
          (Ext.mk₀ s).comp
          (z.comp (a.mapExactFunctor R) (zero_add n)) (zero_add n)) hmk).trans
          ((Ext.mk₀_comp_mk₀_assoc s (R.map m) (a.mapExactFunctor R)).trans
            (congrArg (fun k :
                (constantSheaf W.left.smallEtaleTopology AddCommGrpCat.{u}).obj
                  (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ R.obj P =>
              (Ext.mk₀ k).comp (a.mapExactFunctor R) (zero_add n)) hs)))
  exact hleft.trans (hstep.trans hright.symm)

end EtaleCohomology
