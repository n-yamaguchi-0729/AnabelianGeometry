/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantCoefficientPullback
public import Nyll.EtaleCohomology.Classical.ConstantCoefficientUnit
public import Nyll.EtaleCohomology.Classical.CupProduct
public import Nyll.EtaleCohomology.Classical.CupPullback
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Frobenius.Cohomology
public import Nyll.EtaleCohomology.Sites.ConstantPullback
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Constant cup and the canonical geometric pullback

The existing cup pullback theorem is a theorem for arbitrary second
coefficients. Postcomposing with the canonical constant-sheaf isomorphism
identifies both output coefficients and proves multiplicativity for the
actual constant-coefficient pullback. The identity Ext class supplies its
unit calculation.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Abelian

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]

/-- Actual constant-coefficient pullback preserves native cup products. -/
theorem etaleConstantCohomologyPullbackMap_cup
    (a b c : ℕ) (h : a + b = c)
    (x : etaleCohomology Y R
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) a)
    (y : etaleCohomology Y R
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) b) :
    etaleConstantCohomologyPullbackMap f R (ModuleCat.of R R) c
        (etaleCohomologyCup Y R
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj
            (ModuleCat.of R R)) a b c h x y) =
      etaleCohomologyCup X R
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
          (ModuleCat.of R R)) a b c h
        (etaleConstantCohomologyPullbackMap f R (ModuleCat.of R R) a x)
        (etaleConstantCohomologyPullbackMap f R (ModuleCat.of R R) b y) := by
  let CY := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)
  let e := (etalePullbackConstantIso f R).app (ModuleCat.of R R)
  have hp := etaleCohomologyCup_pullback f R CY a b c h x y
  exact (congrArg (Classical.cohomologyMap e.hom c) hp).trans
    (etaleCohomologyCup_naturality X R e.hom a b c h
      (etaleConstantCohomologyPullbackMap f R (ModuleCat.of R R) a x)
      (etaleCohomologyPullbackMap f R CY b y))

/-- Actual constant-coefficient pullback carries the native cup unit to
the native cup unit. -/
theorem etaleConstantCohomologyPullbackMap_cupUnit :
    etaleConstantCohomologyPullbackMap f R (ModuleCat.of R R) 0
        (etaleCohomologyCupUnit Y R) = etaleCohomologyCupUnit X R := by
  let CY := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)
  let CX := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)
  let L := etalePullback f R
  let e : L.obj CY ≅ CX := (etalePullbackConstantIso f R).app (ModuleCat.of R R)
  let α : Ext.{u} CX (L.obj CY) 0 :=
    (Ext.mk₀ e.inv).comp ((Ext.mk₀ (𝟙 CY)).mapExactFunctor L) (zero_add 0)
  have hp := etaleConstantModuleExtCohomologyEquiv_pullback f R CY 0 (Ext.mk₀ (𝟙 CY))
  have hn := etaleConstantModuleExtCohomologyEquiv_naturality X R e.hom 0 α
  have he : α.comp (Ext.mk₀ e.hom) (add_zero 0) = Ext.mk₀ (𝟙 CX) := by
    change ((Ext.mk₀ e.inv).comp ((Ext.mk₀ (𝟙 CY)).mapExactFunctor L)
      (zero_add 0)).comp (Ext.mk₀ e.hom) (add_zero 0) = _
    rw [Ext.mapExactFunctor_mk₀, L.map_id CY, Ext.comp_mk₀_id,
      Ext.mk₀_comp_mk₀, e.inv_hom_id]
  exact (congrArg (Classical.cohomologyMap e.hom 0) hp).symm.trans
    (hn.symm.trans (congrArg (etaleConstantModuleExtCohomologyEquiv X R CX 0) he))

end EtaleCohomology
