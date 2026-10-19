/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCategories.CoverTransport

/-! # Equivariance on the actual fiber of a transported cover -/

noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

universe u₁ v₁ u₂ v₂ w
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    [GaloisCategory C] [GaloisCategory D]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (G : D ⥤ FintypeCat.{w}) [FiberFunctor G]

/-- Forgetting the transported action gives the actual isomorphism of finite fibers. -/
def coverTransportFiberIso (α : Aut F ≃ₜ* Aut G) (X : C) :
    G.obj ((coverTransportOfAutEquiv F G α).functor.obj X) ≅ F.obj X :=
  (forget₂ (ContAction FintypeCat (Aut G)) FintypeCat).mapIso
    (coverTransportActionIso F G α X)

/-- The actual fiber of the transported cover is equivalent to the original fiber. -/
def coverTransportFiberEquiv (α : Aut F ≃ₜ* Aut G) (X : C) :
    G.obj ((coverTransportOfAutEquiv F G α).functor.obj X) ≃ F.obj X :=
  FintypeCat.equivEquivIso.symm (coverTransportFiberIso F G α X)

@[simp]
lemma coverTransportFiberEquiv_apply (α : Aut F ≃ₜ* Aut G) (X : C)
    (t : G.obj ((coverTransportOfAutEquiv F G α).functor.obj X)) :
    coverTransportFiberEquiv F G α X t =
      (coverTransportActionIso F G α X).hom.hom.hom t := rfl

@[simp]
lemma coverTransportFiberEquiv_symm_apply (α : Aut F ≃ₜ* Aut G) (X : C)
    (t : F.obj X) :
    (coverTransportFiberEquiv F G α X).symm t =
      (coverTransportActionIso F G α X).inv.hom.hom t := rfl

/-- The actual fiber equivalence intertwines the transported fundamental-group action. -/
lemma coverTransportFiberEquiv_smul (α : Aut F ≃ₜ* Aut G) (X : C)
    (g : Aut G) (t : G.obj ((coverTransportOfAutEquiv F G α).functor.obj X)) :
    coverTransportFiberEquiv F G α X (g • t) =
      α.symm g • coverTransportFiberEquiv F G α X t := by
  exact ConcreteCategory.congr_hom
    ((coverTransportActionIso F G α X).hom.hom.comm g) t

/-- Inverse form of the actual fiber equivariance law. -/
lemma coverTransportFiberEquiv_symm_smul (α : Aut F ≃ₜ* Aut G) (X : C)
    (g : Aut G) (t : F.obj X) :
    (coverTransportFiberEquiv F G α X).symm (α.symm g • t) =
      g • (coverTransportFiberEquiv F G α X).symm t := by
  exact ConcreteCategory.congr_hom
    ((coverTransportActionIso F G α X).inv.hom.comm g) t

end CategoryTheory.PreGaloisCategory
