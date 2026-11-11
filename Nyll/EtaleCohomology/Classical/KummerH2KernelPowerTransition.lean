/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.FieldKummer
public import Nyll.EtaleCohomology.Classical.KummerPowerTransition
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Power transitions on the original degree-two Kummer kernels

The actual coefficient maps commute with the original power transition,
which therefore restricts to the original degree-two Kummer kernels.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

/-- The coefficient map from the actual Kummer kernel commutes with the
actual power transition on H². -/
theorem etaleRootsOfUnityH2ToMultiplicativeGroup_powerTransition
    (X : Scheme.{u}) (n m : ℕ)
    (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf X (n * m)) 2) :
    etaleRootsOfUnityH2ToMultiplicativeGroup X n
        (Sheaf.H.map (etaleKummerPowerTransition X n m) 2 a) =
      Sheaf.H.map (etaleMultiplicativeGroupPower X m) 2
        (etaleRootsOfUnityH2ToMultiplicativeGroup X (n * m) a) := by
  change Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower X n)) 2
      (Sheaf.H.map (etaleKummerPowerTransition X n m) 2 a) =
    Sheaf.H.map (etaleMultiplicativeGroupPower X m) 2
      (Sheaf.H.map (kernel.ι (etaleMultiplicativeGroupPower X (n * m))) 2 a)
  rw [← Sheaf.H.map_comp_apply, etaleKummerPowerTransition_ι,
    Sheaf.H.map_comp_apply]

/-- The power map on original roots-of-unity H² restricts to the actual
kernel of the coefficient map to H²(Gm). -/
def etaleKummerH2KernelPowerTransition (X : Scheme.{u}) (n m : ℕ) :
    (etaleRootsOfUnityH2ToMultiplicativeGroup X (n * m)).ker →+
      (etaleRootsOfUnityH2ToMultiplicativeGroup X n).ker :=
  (((Sheaf.H.map (etaleKummerPowerTransition X n m) 2).comp
    (etaleRootsOfUnityH2ToMultiplicativeGroup X (n * m)).ker.subtype).codRestrict
      (etaleRootsOfUnityH2ToMultiplicativeGroup X n).ker fun a => by
        change etaleRootsOfUnityH2ToMultiplicativeGroup X n
          (Sheaf.H.map (etaleKummerPowerTransition X n m) 2 a.val) = 0
        rw [etaleRootsOfUnityH2ToMultiplicativeGroup_powerTransition,
          a.property, map_zero])

/-- The restricted transition has the original H² power map as its
underlying additive homomorphism. -/
theorem etaleKummerH2KernelPowerTransition_val
    (X : Scheme.{u}) (n m : ℕ)
    (a : (etaleRootsOfUnityH2ToMultiplicativeGroup X (n * m)).ker) :
    (etaleKummerH2KernelPowerTransition X n m a).val =
      Sheaf.H.map (etaleKummerPowerTransition X n m) 2 a.val := rfl

end EtaleCohomology
