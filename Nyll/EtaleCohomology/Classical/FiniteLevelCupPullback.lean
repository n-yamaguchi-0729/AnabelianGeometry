/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.ConstantCupPullback
public import Nyll.EtaleCohomology.Classical.CupProduct
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Frobenius.Cohomology
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Pullback preserves original finite-level cups

The actual module-to-abelian comparison identifies native constant
pullback with the original finite-level pullback. Transporting the native
cup and unit calculations through this same comparison proves the
corresponding equalities on the existing finite-level groups.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology.Classical

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The existing constant-module comparison commutes with original
finite-level pullback. -/
theorem finiteLevelConstantModuleEquiv_pullback (n i : ℕ)
    (x : etaleCohomology Y (ULift.{u} (ZMod (ℓ ^ (n + 1))))
      ((constantSheaf Y.smallEtaleTopology
        (ModuleCat.{u} (ULift.{u} (ZMod (ℓ ^ (n + 1)))))).obj
          (ModuleCat.of (ULift.{u} (ZMod (ℓ ^ (n + 1))))
            (ULift.{u} (ZMod (ℓ ^ (n + 1)))))) i) :
    finiteLevelConstantModuleEquiv X ℓ n i
        (etaleConstantCohomologyPullbackMap f (ULift.{u} (ZMod (ℓ ^ (n + 1))))
          (ModuleCat.of (ULift.{u} (ZMod (ℓ ^ (n + 1))))
            (ULift.{u} (ZMod (ℓ ^ (n + 1))))) i x) =
      finiteLevelCohomologyPullback ℓ f n i
        (finiteLevelConstantModuleEquiv Y ℓ n i x) :=
  etaleConstantCohomologyPullbackMap_forget (ULift.{u} (ZMod (ℓ ^ (n + 1)))) f
    (ModuleCat.of (ULift.{u} (ZMod (ℓ ^ (n + 1))))
      (ULift.{u} (ZMod (ℓ ^ (n + 1))))) i x

/-- Original finite-level pullback preserves the original cup product. -/
theorem finiteLevelCohomologyPullback_cup (n a b c : ℕ) (h : a + b = c)
    (x : finiteLevelCohomology Y ℓ n a) (y : finiteLevelCohomology Y ℓ n b) :
    finiteLevelCohomologyPullback ℓ f n c (finiteLevelCup Y ℓ n a b c h x y) =
      finiteLevelCup X ℓ n a b c h
        (finiteLevelCohomologyPullback ℓ f n a x)
        (finiteLevelCohomologyPullback ℓ f n b y) := by
  let R := ULift.{u} (ZMod (ℓ ^ (n + 1)))
  let CY := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let CX := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let ea := finiteLevelConstantModuleEquiv Y ℓ n a
  let eb := finiteLevelConstantModuleEquiv Y ℓ n b
  let da := finiteLevelConstantModuleEquiv X ℓ n a
  let db := finiteLevelConstantModuleEquiv X ℓ n b
  let dc := finiteLevelConstantModuleEquiv X ℓ n c
  have ha : da.symm (finiteLevelCohomologyPullback ℓ f n a x) =
      etaleConstantCohomologyPullbackMap f R (ModuleCat.of R R) a (ea.symm x) := by
    apply da.injective
    rw [AddEquiv.apply_symm_apply]
    exact ((finiteLevelConstantModuleEquiv_pullback ℓ f n a (ea.symm x)).trans
      (congrArg (finiteLevelCohomologyPullback ℓ f n a) (ea.apply_symm_apply x))).symm
  have hb : db.symm (finiteLevelCohomologyPullback ℓ f n b y) =
      etaleConstantCohomologyPullbackMap f R (ModuleCat.of R R) b (eb.symm y) := by
    apply db.injective
    rw [AddEquiv.apply_symm_apply]
    exact ((finiteLevelConstantModuleEquiv_pullback ℓ f n b (eb.symm y)).trans
      (congrArg (finiteLevelCohomologyPullback ℓ f n b) (eb.apply_symm_apply y))).symm
  calc
    _ = dc (etaleConstantCohomologyPullbackMap f R (ModuleCat.of R R) c
        (etaleCohomologyCup Y R CY a b c h (ea.symm x) (eb.symm y))) :=
      (finiteLevelConstantModuleEquiv_pullback ℓ f n c
        (etaleCohomologyCup Y R CY a b c h (ea.symm x) (eb.symm y))).symm
    _ = dc (etaleCohomologyCup X R CX a b c h
        (etaleConstantCohomologyPullbackMap f R (ModuleCat.of R R) a (ea.symm x))
        (etaleConstantCohomologyPullbackMap f R (ModuleCat.of R R) b (eb.symm y))) :=
      congrArg dc (etaleConstantCohomologyPullbackMap_cup f R a b c h (ea.symm x) (eb.symm y))
    _ = _ := by
      rw [finiteLevelCup_apply, ha, hb]

/-- Original finite-level pullback carries the cup unit to the cup unit. -/
theorem finiteLevelCohomologyPullback_cupUnit (n : ℕ) :
    finiteLevelCohomologyPullback ℓ f n 0 (finiteLevelCupUnit Y ℓ n) =
      finiteLevelCupUnit X ℓ n := by
  simp only [finiteLevelCupUnit, ← finiteLevelConstantModuleEquiv_pullback,
    etaleConstantCohomologyPullbackMap_cupUnit]

end EtaleCohomology.Classical
