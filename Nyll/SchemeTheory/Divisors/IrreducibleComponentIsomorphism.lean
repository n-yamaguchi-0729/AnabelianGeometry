/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Divisors.IrreducibleComponentMap
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.Irreducible

/-!
# Actual isomorphisms on the original reduced components

An original scheme isomorphism permutes its original irreducible
components. The existing reduced-component morphism gives actual
scheme isomorphisms on the corresponding reduced components. Both
inclusions and the original scheme morphisms are retained, without
choosing substitute component schemes or a component trivialization.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (e : X ≅ Y)

/-- The original scheme isomorphism acts on the actual component
index by its actual image map. -/
def irreducibleComponentsIsoEquiv : irreducibleComponents X ≃ irreducibleComponents Y :=
  (irreducibleComponentsEquivOfIsPreirreducibleFiber e.hom e.hom.continuous
    e.hom.homeomorph.isOpenMap
    (fun y => ((Set.subsingleton_singleton (a := y)).preimage
      e.hom.homeomorph.injective).isPreirreducible)
    e.hom.homeomorph.surjective).toEquiv.symm

/-- The component permutation retains the actual image subset. -/
theorem irreducibleComponentsIsoEquiv_coe (Z : irreducibleComponents X) :
    (irreducibleComponentsIsoEquiv e Z).1 = e.hom '' Z.1 := rfl

/-- The original inverse morphism takes that same image component
back to its original source component. -/
theorem irreducibleComponentsIsoEquiv_inv_image (Z : irreducibleComponents X) :
    e.inv '' (irreducibleComponentsIsoEquiv e Z).1 = Z.1 := by
  rw [irreducibleComponentsIsoEquiv_coe, Set.image_image]
  have hcomp : (fun x : X => e.inv (e.hom x)) = id := by
    funext x
    exact congrArg (fun f : X ⟶ X => f x) e.hom_inv_id
  rw [hcomp, Set.image_id]

/-- The original reduced-component maps in both directions are
inverse scheme morphisms. -/
def reducedIrreducibleComponentIso (Z : irreducibleComponents X) :
    X.reducedIrreducibleComponent Z.1 Z.2 ≅
      Y.reducedIrreducibleComponent (irreducibleComponentsIsoEquiv e Z).1
        (irreducibleComponentsIsoEquiv e Z).2 where
  hom := X.reducedIrreducibleComponentMap e.hom Z.1 Z.2
    (irreducibleComponentsIsoEquiv e Z).1 (irreducibleComponentsIsoEquiv e Z).2
    (irreducibleComponentsIsoEquiv_coe e Z).symm
  inv := Y.reducedIrreducibleComponentMap e.inv
    (irreducibleComponentsIsoEquiv e Z).1 (irreducibleComponentsIsoEquiv e Z).2
    Z.1 Z.2 (irreducibleComponentsIsoEquiv_inv_image e Z)
  hom_inv_id := by
    apply (cancel_mono (X.reducedIrreducibleComponentι Z.1 Z.2)).mp
    rw [Category.assoc, reducedIrreducibleComponentMap_ι, ← Category.assoc,
      reducedIrreducibleComponentMap_ι, Category.assoc, e.hom_inv_id,
      Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (Y.reducedIrreducibleComponentι
      (irreducibleComponentsIsoEquiv e Z).1 (irreducibleComponentsIsoEquiv e Z).2)).mp
    rw [Category.assoc, reducedIrreducibleComponentMap_ι, ← Category.assoc,
      reducedIrreducibleComponentMap_ι, Category.assoc, e.inv_hom_id,
      Category.comp_id, Category.id_comp]

/-- The actual component isomorphism commutes with the original
scheme isomorphism and the two original component inclusions. -/
theorem reducedIrreducibleComponentIso_hom_ι (Z : irreducibleComponents X) :
    (reducedIrreducibleComponentIso e Z).hom ≫
        Y.reducedIrreducibleComponentι (irreducibleComponentsIsoEquiv e Z).1
          (irreducibleComponentsIsoEquiv e Z).2 =
      X.reducedIrreducibleComponentι Z.1 Z.2 ≫ e.hom :=
  reducedIrreducibleComponentMap_ι e.hom Z.1 Z.2
    (irreducibleComponentsIsoEquiv e Z).1 (irreducibleComponentsIsoEquiv e Z).2
    (irreducibleComponentsIsoEquiv_coe e Z).symm

/-- The inverse component isomorphism retains the original inverse
scheme map and the same original inclusions. -/
theorem reducedIrreducibleComponentIso_inv_ι (Z : irreducibleComponents X) :
    (reducedIrreducibleComponentIso e Z).inv ≫
        X.reducedIrreducibleComponentι Z.1 Z.2 =
      Y.reducedIrreducibleComponentι (irreducibleComponentsIsoEquiv e Z).1
        (irreducibleComponentsIsoEquiv e Z).2 ≫ e.inv :=
  reducedIrreducibleComponentMap_ι e.inv
    (irreducibleComponentsIsoEquiv e Z).1 (irreducibleComponentsIsoEquiv e Z).2
    Z.1 Z.2 (irreducibleComponentsIsoEquiv_inv_image e Z)

end AlgebraicGeometry.Scheme
