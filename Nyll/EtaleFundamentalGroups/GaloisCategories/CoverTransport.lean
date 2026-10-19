/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Galois.Equivalence

/-! # Actual cover transport from an isomorphism of fundamental groups -/

noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

universe u₁ v₁ u₂ v₂ w
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    [GaloisCategory C] [GaloisCategory D]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (G : D ⥤ FintypeCat.{w}) [FiberFunctor G]

/-- Construct cover transport from the given topological group isomorphism. -/
def coverTransportOfAutEquiv (α : Aut F ≃ₜ* Aut G) : C ≌ D :=
  (functorToContAction F).asEquivalence.trans
    ((ContAction.resEquiv FintypeCat α.symm).trans (functorToContAction G).asEquivalence.symm)

/-- The transported cover has precisely its transported finite action. -/
def coverTransportActionIso (α : Aut F ≃ₜ* Aut G) (X : C) :
    (functorToContAction G).obj ((coverTransportOfAutEquiv F G α).functor.obj X) ≅
      (ContAction.resEquiv FintypeCat α.symm).functor.obj ((functorToContAction F).obj X) :=
  (functorToContAction G).asEquivalence.counitIso.app _

end CategoryTheory.PreGaloisCategory
