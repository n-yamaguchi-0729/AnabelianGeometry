/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.KummerPowerTransition
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Pullback and power transitions on the original Kummer kernels

The power transition commutes with the actual inverse-image map on the
roots-of-unity sheaves. This yields the compatibility in every cohomological
degree before taking any kernel, inverse limit, or rationalization.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The original power transition commutes with inverse image of the
actual roots-of-unity kernels. -/
theorem etaleRootsOfUnityPullback_powerTransition (n m : ℕ) :
    (etaleAbelianPullback f).map (etaleKummerPowerTransition Y n m) ≫
        etaleRootsOfUnityPullback f n =
      etaleRootsOfUnityPullback f (n * m) ≫
        etaleKummerPowerTransition X n m := by
  apply (cancel_mono (kernel.ι (etaleMultiplicativeGroupPower X n))).1
  rw [Category.assoc, etaleRootsOfUnityPullback_ι,
    ← Category.assoc, ← Functor.map_comp, etaleKummerPowerTransition_ι,
    Functor.map_comp, Category.assoc, etaleMultiplicativeGroupPullback_power,
    ← Category.assoc, ← etaleRootsOfUnityPullback_ι]
  simp only [Category.assoc, etaleKummerPowerTransition_ι]

/-- In every degree, actual cohomological pullback commutes with the
power transition on the original roots-of-unity coefficients. -/
theorem etaleRootsOfUnityCohomologyPullback_powerTransition
    (n m i : ℕ) (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf Y (n * m)) i) :
    Sheaf.H.map (etaleKummerPowerTransition X n m) i
        (etaleRootsOfUnityCohomologyPullback f (n * m) i a) =
      etaleRootsOfUnityCohomologyPullback f n i
        (Sheaf.H.map (etaleKummerPowerTransition Y n m) i a) := by
  change Sheaf.H.map (etaleKummerPowerTransition X n m) i
      (Sheaf.H.map (etaleRootsOfUnityPullback f (n * m)) i
        (etaleAbelianCohomologyPullbackMap f (etaleRootsOfUnitySheaf Y (n * m)) i a)) =
    Sheaf.H.map (etaleRootsOfUnityPullback f n) i
      (etaleAbelianCohomologyPullbackMap f (etaleRootsOfUnitySheaf Y n) i
        (Sheaf.H.map (etaleKummerPowerTransition Y n m) i a))
  rw [etaleAbelianCohomologyPullbackMap_naturality,
    ← Sheaf.H.map_comp_apply, ← etaleRootsOfUnityPullback_powerTransition,
    Sheaf.H.map_comp_apply]

end EtaleCohomology
