/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantCoefficientPullback
public import Nyll.EtaleCohomology.Classical.ConstantCoefficientUnit
public import Nyll.EtaleCohomology.Classical.CupProduct
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Frobenius.Cohomology
public import Nyll.EtaleCohomology.Sites.ConstantPullback
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# The actual Yoneda cup action commutes with geometric pullback

The original source comparison isomorphism and the actual constant-sheaf
pullback comparison identify both factors. Exact inverse image preserves
Yoneda composition, and its intervening constant-sheaf isomorphisms cancel.
No comparison square or cohomological identification is an input.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

private theorem ext_iso_comp
    {C : Type*} [Category* C] [Abelian C] [HasExt.{u} C]
    {A B F : C} (e : A ≅ B) {a b c : ℕ} (h : a + b = c)
    (α : Ext.{u} A A a) (β : Ext.{u} A F b) :
    (((Ext.mk₀ e.inv).comp α (zero_add a)).comp (Ext.mk₀ e.hom) (add_zero a)).comp
        ((Ext.mk₀ e.inv).comp β (zero_add b)) h =
      (Ext.mk₀ e.inv).comp (α.comp β h) (zero_add c) := by
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀_assoc,
    e.hom_inv_id, Ext.mk₀_id_comp]
  exact Ext.comp_assoc (Ext.mk₀ e.inv) α β (zero_add a) h
    (by simpa only [zero_add] using h)

/-- The cup action on the original module étale cohomology commutes with
actual scheme pullback, including the canonical constant coefficient map. -/
theorem etaleCohomologyCup_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R))
    (a b c : ℕ) (h : a + b = c)
    (x : etaleCohomology Y R
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) a)
    (y : etaleCohomology Y R F b) :
    etaleCohomologyPullbackMap f R F c (etaleCohomologyCup Y R F a b c h x y) =
      etaleCohomologyCup X R ((etalePullback f R).obj F) a b c h
        (etaleConstantCohomologyPullbackMap f R (ModuleCat.of R R) a x)
        (etaleCohomologyPullbackMap f R F b y) := by
  let CY := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)
  let CX := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)
  let L := etalePullback f R
  let e : L.obj CY ≅ CX := (etalePullbackConstantIso f R).app (ModuleCat.of R R)
  let EYa : Ext.{u} CY CY a ≃ₗ[R] etaleCohomology Y R CY a :=
    etaleConstantModuleExtCohomologyEquiv Y R CY a
  let EYb : Ext.{u} CY F b ≃ₗ[R] etaleCohomology Y R F b :=
    etaleConstantModuleExtCohomologyEquiv Y R F b
  let EYc : Ext.{u} CY F c ≃ₗ[R] etaleCohomology Y R F c :=
    etaleConstantModuleExtCohomologyEquiv Y R F c
  let EXa : Ext.{u} CX CX a ≃ₗ[R] etaleCohomology X R CX a :=
    etaleConstantModuleExtCohomologyEquiv X R CX a
  let EXb : Ext.{u} CX (L.obj F) b ≃ₗ[R] etaleCohomology X R (L.obj F) b :=
    etaleConstantModuleExtCohomologyEquiv X R (L.obj F) b
  let EXc : Ext.{u} CX (L.obj F) c ≃ₗ[R] etaleCohomology X R (L.obj F) c :=
    etaleConstantModuleExtCohomologyEquiv X R (L.obj F) c
  let α : Ext.{u} CY CY a := EYa.symm x
  let β : Ext.{u} CY F b := EYb.symm y
  let α' : Ext.{u} CX CX a :=
    ((Ext.mk₀ e.inv).comp (α.mapExactFunctor L) (zero_add a)).comp
      (Ext.mk₀ e.hom) (add_zero a)
  let β' : Ext.{u} CX (L.obj F) b :=
    (Ext.mk₀ e.inv).comp (β.mapExactFunctor L) (zero_add b)
  have hα : EXa α' = etaleConstantCohomologyPullbackMap f R (ModuleCat.of R R) a x := by
    have hn := etaleConstantModuleExtCohomologyEquiv_naturality X R e.hom a
      ((Ext.mk₀ e.inv).comp (α.mapExactFunctor L) (zero_add a))
    have hp := etaleConstantModuleExtCohomologyEquiv_pullback f R CY a α
    have hx : EYa α = x := EYa.apply_symm_apply x
    exact hn.trans ((congrArg (fun z : etaleCohomology X R (L.obj CY) a =>
      Classical.cohomologyMap e.hom a z) hp).trans
        (congrArg (fun z : etaleCohomology Y R CY a =>
          etaleConstantCohomologyPullbackMap f R (ModuleCat.of R R) a z) hx))
  have hβ : EXb β' = etaleCohomologyPullbackMap f R F b y :=
    (etaleConstantModuleExtCohomologyEquiv_pullback f R F b β).trans
      (congrArg (etaleCohomologyPullbackMap f R F b) (EYb.apply_symm_apply y))
  have hcomp : α'.comp β' h =
      (Ext.mk₀ e.inv).comp ((α.comp β h).mapExactFunctor L) (zero_add c) :=
    (ext_iso_comp e h (α.mapExactFunctor L) (β.mapExactFunctor L)).trans
      (congrArg (fun z : Ext.{u} (L.obj CY) (L.obj F) c =>
        (Ext.mk₀ e.inv).comp z (zero_add c))
          (Ext.mapExactFunctor_comp L α β h).symm)
  have hcupX : etaleCohomologyCup X R (L.obj F) a b c h (EXa α') (EXb β') =
      EXc (α'.comp β' h) := by
    rw [etaleCohomologyCup_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]
  calc
    _ = etaleCohomologyPullbackMap f R F c (EYc (α.comp β h)) := rfl
    _ = EXc ((Ext.mk₀ e.inv).comp ((α.comp β h).mapExactFunctor L) (zero_add c)) :=
      (etaleConstantModuleExtCohomologyEquiv_pullback f R F c (α.comp β h)).symm
    _ = EXc (α'.comp β' h) := congrArg EXc hcomp.symm
    _ = etaleCohomologyCup X R (L.obj F) a b c h (EXa α') (EXb β') := hcupX.symm
    _ = _ := congrArg₂
      (fun (u : etaleCohomology X R CX a) (v : etaleCohomology X R (L.obj F) b) =>
        etaleCohomologyCup X R (L.obj F) a b c h u v) hα hβ

end EtaleCohomology
