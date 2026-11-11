/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.CoefficientSheaves
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Classical.ModuleExtCohomology
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Classical.PullbackCoefficients
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Nyll.EtaleCohomology.Sites.PullbackStalks
public import Nyll.SchemeTheory.HomologicalAlgebra.ExtAdjunctionAcyclic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The original module Ext comparison respects geometric pullback

The existing coefficient adjunction constructs the source morphism for
module Ext pullback. Its adjunct is the original constant-integer pullback
followed by the actual coefficient-forgetting comparison. Naturality of
the exact-functor Ext map then identifies this map with classical pullback
in every degree. No preservation of injectives is required here.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

private theorem adjunctionExtMap_precomp_mk₀
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasExt.{u} C] [HasExt.{u} D] {L : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : L ⊣ G) (Z : C) {A B : D} (a : L.obj Z ⟶ A)
    {n : ℕ} (x : Ext.{u} A B n) :
    adj.extMapOfExactRight Z B n ((Ext.mk₀ a).comp x (zero_add n)) =
      (Ext.mk₀ (adj.homEquiv Z A a)).comp (x.mapExactFunctor G) (zero_add n) := by
  exact (adj.extMapOfExactRight_comp Z (Ext.mk₀ a) x (zero_add n)).trans
    (congrArg (fun e : Ext.{u} Z (G.obj A) 0 =>
      e.comp (x.mapExactFunctor G) (zero_add n))
      (adj.extMapOfExactRight_mk₀ Z a))

private theorem exactFunctorPullback_extSquare
    {C D E H : Type*} [Category* C] [Category* D] [Category* E] [Category* H]
    [Abelian C] [Abelian D] [Abelian E] [Abelian H]
    [HasExt.{u} C] [HasExt.{u} D] [HasExt.{u} E] [HasExt.{u} H]
    (UY : C ⥤ E) (UX : D ⥤ H) (L : C ⥤ D) (La : E ⥤ H)
    [UY.Additive] [UX.Additive] [L.Additive] [La.Additive]
    [PreservesFiniteLimits UY] [PreservesFiniteColimits UY]
    [PreservesFiniteLimits UX] [PreservesFiniteColimits UX]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits La] [PreservesFiniteColimits La]
    (ε : UY ⋙ La ⟶ L ⋙ UX) {AY F : C} {ZY : E} {ZX : H}
    (b : ZX ⟶ La.obj ZY) (η : ZY ⟶ UY.obj AY) {n : ℕ} (x : Ext.{u} AY F n) :
    (Ext.mk₀ (b ≫ La.map η ≫ ε.app AY)).comp
        ((x.mapExactFunctor L).mapExactFunctor UX) (zero_add n) =
      ((Ext.mk₀ b).comp
        (((Ext.mk₀ η).comp (x.mapExactFunctor UY) (zero_add n)).mapExactFunctor La)
          (zero_add n)).comp (Ext.mk₀ (ε.app F)) (add_zero n) := by
  have hU : x.mapExactFunctor (UY ⋙ La) =
      ((x.mapExactFunctor UY : Ext.{u} (UY.obj AY) (UY.obj F) n).mapExactFunctor La :
        Ext.{u} (La.obj (UY.obj AY)) (La.obj (UY.obj F)) n) :=
    Ext.comp_mapExactFunctor x UY La
  have hL : x.mapExactFunctor (L ⋙ UX) =
      ((x.mapExactFunctor L : Ext.{u} (L.obj AY) (L.obj F) n).mapExactFunctor UX :
        Ext.{u} (UX.obj (L.obj AY)) (UX.obj (L.obj F)) n) :=
    Ext.comp_mapExactFunctor x L UX
  have hε :
      ((x.mapExactFunctor UY).mapExactFunctor La).comp
          (Ext.mk₀ (ε.app F)) (add_zero n) =
        (Ext.mk₀ (ε.app AY)).comp
          ((x.mapExactFunctor L).mapExactFunctor UX) (zero_add n) :=
    (congrArg (fun e : Ext.{u} (La.obj (UY.obj AY)) (La.obj (UY.obj F)) n =>
      e.comp (Ext.mk₀ (ε.app F)) (add_zero n)) hU.symm).trans
        ((Ext.mapExactFunctor_comp_mk₀_natTransApp x ε).trans
          (congrArg (fun e : Ext.{u} (UX.obj (L.obj AY)) (UX.obj (L.obj F)) n =>
            (Ext.mk₀ (ε.app AY)).comp e (zero_add n)) hL))
  symm
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero, hε,
    Ext.mk₀_comp_mk₀_assoc, Category.assoc]

private theorem adjunctionExtMap_apply
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasExt.{u} C] [HasExt.{u} D] {L : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : L ⊣ G) (Z : C) (F : D) {n : ℕ} (x : Ext.{u} (L.obj Z) F n) :
    adj.extMapOfExactRight Z F n x =
      (Ext.mk₀ (adj.homEquiv Z (L.obj Z) (𝟙 _))).comp
        (x.mapExactFunctor G) (zero_add n) := by
  simpa only [Ext.mk₀_id_comp] using
    adjunctionExtMap_precomp_mk₀ adj Z (𝟙 (L.obj Z)) x

private theorem adjunctionExtMap_pullback
    {C D E H : Type*} [Category* C] [Category* D] [Category* E] [Category* H]
    [Abelian C] [Abelian D] [Abelian E] [Abelian H]
    [HasExt.{u} C] [HasExt.{u} D] [HasExt.{u} E] [HasExt.{u} H]
    {EY : E ⥤ C} {EX : H ⥤ D} {UY : C ⥤ E} {UX : D ⥤ H}
    (adjY : EY ⊣ UY) (adjX : EX ⊣ UX) (L : C ⥤ D) (La : E ⥤ H)
    [UY.Additive] [UX.Additive] [L.Additive] [La.Additive]
    [PreservesFiniteLimits UY] [PreservesFiniteColimits UY]
    [PreservesFiniteLimits UX] [PreservesFiniteColimits UX]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits La] [PreservesFiniteColimits La]
    (ε : UY ⋙ La ⟶ L ⋙ UX) (ZY : E) (ZX : H)
    (b : ZX ⟶ La.obj ZY) (a : EX.obj ZX ⟶ L.obj (EY.obj ZY))
    (ha : adjX.homEquiv ZX (L.obj (EY.obj ZY)) a =
      b ≫ La.map (adjY.homEquiv ZY (EY.obj ZY) (𝟙 _)) ≫ ε.app (EY.obj ZY))
    {F : C} {n : ℕ} (x : Ext.{u} (EY.obj ZY) F n) :
    adjX.extMapOfExactRight ZX (L.obj F) n
        ((Ext.mk₀ a).comp (x.mapExactFunctor L) (zero_add n)) =
      ((Ext.mk₀ b).comp
        ((adjY.extMapOfExactRight ZY F n x).mapExactFunctor La) (zero_add n)).comp
          (Ext.mk₀ (ε.app F)) (add_zero n) := by
  let η := adjY.homEquiv ZY (EY.obj ZY) (𝟙 _)
  have hη : adjY.extMapOfExactRight ZY F n x =
      (Ext.mk₀ η).comp (x.mapExactFunctor UY) (zero_add n) :=
    adjunctionExtMap_apply adjY ZY F x
  calc
    _ = (Ext.mk₀ (adjX.homEquiv ZX (L.obj (EY.obj ZY)) a)).comp
        ((x.mapExactFunctor L).mapExactFunctor UX) (zero_add n) :=
      adjunctionExtMap_precomp_mk₀ adjX ZX a (x.mapExactFunctor L)
    _ = (Ext.mk₀ (b ≫ La.map η ≫ ε.app (EY.obj ZY))).comp
        ((x.mapExactFunctor L).mapExactFunctor UX) (zero_add n) :=
      congrArg (fun q : ZX ⟶ UX.obj (L.obj (EY.obj ZY)) =>
        (Ext.mk₀ q).comp ((x.mapExactFunctor L).mapExactFunctor UX) (zero_add n)) ha
    _ = ((Ext.mk₀ b).comp
        (((Ext.mk₀ η).comp (x.mapExactFunctor UY) (zero_add n)).mapExactFunctor La)
          (zero_add n)).comp (Ext.mk₀ (ε.app F)) (add_zero n) :=
      exactFunctorPullback_extSquare UY UX L La ε b η x
    _ = _ := congrArg (fun e : Ext.{u} ZY (UY.obj F) n =>
      ((Ext.mk₀ b).comp (e.mapExactFunctor La) (zero_add n)).comp
        (Ext.mk₀ (ε.app F)) (add_zero n)) hη.symm

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]

/-- The source morphism for module Ext pullback, constructed through the
original coefficient adjunction from the actual constant-sheaf comparison. -/
def etaleModuleFreeIntegerPullbackHom :
    etaleFreeIntegerModuleSheaf X R ⟶
      (etalePullback f R).obj (etaleFreeIntegerModuleSheaf Y R) :=
  (etaleModuleIntegerHomForgetEquiv X R
    ((etalePullback f R).obj (etaleFreeIntegerModuleSheaf Y R))).symm
      (((etaleAbelianPullbackConstantIso f).app (AddCommGrpCat.of (ULift.{u} ℤ))).inv ≫
        (etaleAbelianPullback f).map
          (etaleModuleIntegerHomForgetEquiv Y R (etaleFreeIntegerModuleSheaf Y R) (𝟙 _)) ≫
        (etalePullbackForgetCoefficientsIso f R).inv.app (etaleFreeIntegerModuleSheaf Y R))

/-- The constructed source morphism retains its actual adjunct. -/
theorem etaleModuleFreeIntegerPullbackHom_adjunct :
    etaleModuleIntegerHomForgetEquiv X R
        ((etalePullback f R).obj (etaleFreeIntegerModuleSheaf Y R))
        (etaleModuleFreeIntegerPullbackHom f R) =
      ((etaleAbelianPullbackConstantIso f).app (AddCommGrpCat.of (ULift.{u} ℤ))).inv ≫
        (etaleAbelianPullback f).map
          (etaleModuleIntegerHomForgetEquiv Y R (etaleFreeIntegerModuleSheaf Y R) (𝟙 _)) ≫
        (etalePullbackForgetCoefficientsIso f R).inv.app (etaleFreeIntegerModuleSheaf Y R) :=
  (etaleModuleIntegerHomForgetEquiv X R
    ((etalePullback f R).obj (etaleFreeIntegerModuleSheaf Y R))).apply_symm_apply _

/-- Module Ext pullback through the constructed source morphism agrees
with the original classical pullback in every degree. -/
theorem etaleModuleExtCohomologyMap_pullback
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ)
    (x : Ext.{u} (etaleFreeIntegerModuleSheaf Y R) F n) :
    etaleModuleExtCohomologyMap X R ((etalePullback f R).obj F) n
        ((Ext.mk₀ (etaleModuleFreeIntegerPullbackHom f R)).comp
          (x.mapExactFunctor (etalePullback f R)) (zero_add n)) =
      etaleCohomologyPullbackMap f R F n (etaleModuleExtCohomologyMap Y R F n x) := by
  change _ =
    ((Ext.mk₀ (((etaleAbelianPullbackConstantIso f).app
      (AddCommGrpCat.of (ULift.{u} ℤ))).inv)).comp
        ((etaleModuleExtCohomologyMap Y R F n x).mapExactFunctor
          (etaleAbelianPullback f)) (zero_add n)).comp
            (Ext.mk₀ ((etalePullbackForgetCoefficientsIso f R).inv.app F)) (add_zero n)
  unfold etaleModuleExtCohomologyMap
  exact adjunctionExtMap_pullback _ _ (etalePullback f R) (etaleAbelianPullback f)
    (etalePullbackForgetCoefficientsIso f R).inv _ _ _
    (etaleModuleFreeIntegerPullbackHom f R)
    (etaleModuleFreeIntegerPullbackHom_adjunct f R) x

end EtaleCohomology
