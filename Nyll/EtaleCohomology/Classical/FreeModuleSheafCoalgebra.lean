/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupTensorAdditive
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Comon_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Sites.Monoidal

/-!
# The actual diagonal on free module sheaves

The original free module functor and the original sheafification carry
the Cartesian diagonal to a comonoid on the actual free module sheaf.
Its pairing multiplies two maps on the same generator. In particular,
the tensor unit acts on a module sheaf without identifying its locally
constant sections with scalars in the coefficient ring.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped EtaleCohomology.ModuleTensor

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- The original pointwise free module functor on type-valued presheaves. -/
abbrev freeModulePresheafFunctor :
    (X.Etaleᵒᵖ ⥤ Type u) ⥤ (X.Etaleᵒᵖ ⥤ ModuleCat.{u} R) :=
  (Functor.whiskeringRight _ _ _).obj (ModuleCat.free R)

/-- The original free module sheaf on a type-valued presheaf. -/
abbrev freeModuleSheafFunctor :
    (X.Etaleᵒᵖ ⥤ Type u) ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
  freeModulePresheafFunctor X R ⋙
    presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)

/-- The Cartesian diagonal, carried by the actual free module functor. -/
def freeModulePresheafCoalgebra :
    (X.Etaleᵒᵖ ⥤ Type u) ⥤ Comon (X.Etaleᵒᵖ ⥤ ModuleCat.{u} R) :=
  cartesianComon _ ⋙ (freeModulePresheafFunctor X R).mapComon

/-- The actual sheafified coalgebra, with the original sheaf tensor. -/
def freeModuleSheafCoalgebra :
    (X.Etaleᵒᵖ ⥤ Type u) ⥤ Comon (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  freeModulePresheafCoalgebra X R ⋙
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapComon

/-- The diagonal of the actual free module sheaf. -/
def freeModuleSheafDiagonal (P : X.Etaleᵒᵖ ⥤ Type u) :
    (freeModuleSheafFunctor X R).obj P ⟶
      (freeModuleSheafFunctor X R).obj P ⊗ (freeModuleSheafFunctor X R).obj P :=
  ((freeModuleSheafCoalgebra X R).obj P).comon.comul

/-- The augmentation to the original regular constant coefficient sheaf. -/
def freeModuleSheafCounit (P : X.Etaleᵒᵖ ⥤ Type u) :
    (freeModuleSheafFunctor X R).obj P ⟶
      𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  ((freeModuleSheafCoalgebra X R).obj P).comon.counit

/-- The actual diagonal commutes with the original free sheaf maps. -/
theorem freeModuleSheafDiagonal_naturality
    {P Q : X.Etaleᵒᵖ ⥤ Type u} (η : P ⟶ Q) :
    (freeModuleSheafFunctor X R).map η ≫ freeModuleSheafDiagonal X R Q =
      freeModuleSheafDiagonal X R P ≫
        ((freeModuleSheafFunctor X R).map η ⊗ₘ (freeModuleSheafFunctor X R).map η) := by
  exact IsComonHom.hom_comul ((freeModuleSheafCoalgebra X R).map η).hom

/-- The actual augmentation commutes with the original free sheaf maps. -/
theorem freeModuleSheafCounit_naturality
    {P Q : X.Etaleᵒᵖ ⥤ Type u} (η : P ⟶ Q) :
    (freeModuleSheafFunctor X R).map η ≫ freeModuleSheafCounit X R Q =
      freeModuleSheafCounit X R P := by
  exact IsComonHom.hom_counit ((freeModuleSheafCoalgebra X R).map η).hom

variable {P : X.Etaleᵒᵖ ⥤ Type u}
  {E F G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}

/-- Pairing two maps on the same actual free generator. -/
def freeModuleSheafPairing
    (a : (freeModuleSheafFunctor X R).obj P ⟶ E)
    (b : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    (freeModuleSheafFunctor X R).obj P ⟶ E ⊗ F :=
  freeModuleSheafDiagonal X R P ≫ (a ⊗ₘ b)

/-- Pairing respects actual maps of type-valued presheaves. -/
theorem freeModuleSheafPairing_precomp {Q : X.Etaleᵒᵖ ⥤ Type u} (η : Q ⟶ P)
    (a : (freeModuleSheafFunctor X R).obj P ⟶ E)
    (b : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    (freeModuleSheafFunctor X R).map η ≫ freeModuleSheafPairing X R a b =
      freeModuleSheafPairing X R
        ((freeModuleSheafFunctor X R).map η ≫ a)
        ((freeModuleSheafFunctor X R).map η ≫ b) := by
  unfold freeModuleSheafPairing
  rw [← Category.assoc, freeModuleSheafDiagonal_naturality,
    Category.assoc, tensorHom_comp_tensorHom]

/-- Pairing retains the original maps of coefficient sheaves. -/
theorem freeModuleSheafPairing_postcomp
    (a : (freeModuleSheafFunctor X R).obj P ⟶ E)
    (b : (freeModuleSheafFunctor X R).obj P ⟶ F) (g : E ⟶ G) (h : F ⟶ H) :
    freeModuleSheafPairing X R a b ≫ (g ⊗ₘ h) =
      freeModuleSheafPairing X R (a ≫ g) (b ≫ h) := by
  unfold freeModuleSheafPairing
  rw [Category.assoc, tensorHom_comp_tensorHom]

theorem freeModuleSheafPairing_add_left
    (a a' : (freeModuleSheafFunctor X R).obj P ⟶ E)
    (b : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    freeModuleSheafPairing X R (a + a') b =
      freeModuleSheafPairing X R a b + freeModuleSheafPairing X R a' b := by
  unfold freeModuleSheafPairing
  rw [MonoidalPreadditive.add_tensor, Preadditive.comp_add]

theorem freeModuleSheafPairing_add_right
    (a : (freeModuleSheafFunctor X R).obj P ⟶ E)
    (b b' : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    freeModuleSheafPairing X R a (b + b') =
      freeModuleSheafPairing X R a b + freeModuleSheafPairing X R a b' := by
  unfold freeModuleSheafPairing
  rw [MonoidalPreadditive.tensor_add, Preadditive.comp_add]

theorem freeModuleSheafPairing_sub_left
    (a a' : (freeModuleSheafFunctor X R).obj P ⟶ E)
    (b : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    freeModuleSheafPairing X R (a - a') b =
      freeModuleSheafPairing X R a b - freeModuleSheafPairing X R a' b := by
  apply (eq_sub_iff_add_eq).mpr
  rw [← freeModuleSheafPairing_add_left, sub_add_cancel]

theorem freeModuleSheafPairing_sub_right
    (a : (freeModuleSheafFunctor X R).obj P ⟶ E)
    (b b' : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    freeModuleSheafPairing X R a (b - b') =
      freeModuleSheafPairing X R a b - freeModuleSheafPairing X R a b' := by
  apply (eq_sub_iff_add_eq).mpr
  rw [← freeModuleSheafPairing_add_right, sub_add_cancel]

/-- The left counit law is the actual inverse left unitor. -/
theorem freeModuleSheafPairing_counit_left
    (b : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    freeModuleSheafPairing X R (freeModuleSheafCounit X R P) b = b ≫ (λ_ F).inv := by
  exact ComonObj.counit_comul_hom (M := ((freeModuleSheafCoalgebra X R).obj P).X) b

/-- The right counit law is the actual inverse right unitor. -/
theorem freeModuleSheafPairing_counit_right
    (a : (freeModuleSheafFunctor X R).obj P ⟶ E) :
    freeModuleSheafPairing X R a (freeModuleSheafCounit X R P) = a ≫ (ρ_ E).inv := by
  exact ComonObj.comul_counit_hom (M := ((freeModuleSheafCoalgebra X R).obj P).X) a

/-- Multiplication of an actual locally constant coefficient with an
actual module-sheaf section, through the native tensor unit. -/
def freeModuleSheafAction
    (a : (freeModuleSheafFunctor X R).obj P ⟶
      𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)))
    (b : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    (freeModuleSheafFunctor X R).obj P ⟶ F :=
  freeModuleSheafPairing X R a b ≫ (λ_ F).hom

theorem freeModuleSheafAction_precomp {Q : X.Etaleᵒᵖ ⥤ Type u} (η : Q ⟶ P)
    (a : (freeModuleSheafFunctor X R).obj P ⟶
      𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)))
    (b : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    (freeModuleSheafFunctor X R).map η ≫ freeModuleSheafAction X R a b =
      freeModuleSheafAction X R
        ((freeModuleSheafFunctor X R).map η ≫ a)
        ((freeModuleSheafFunctor X R).map η ≫ b) := by
  unfold freeModuleSheafAction
  rw [← Category.assoc, freeModuleSheafPairing_precomp]

theorem freeModuleSheafAction_postcomp
    (a : (freeModuleSheafFunctor X R).obj P ⟶
      𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)))
    (b : (freeModuleSheafFunctor X R).obj P ⟶ F) (h : F ⟶ H) :
    freeModuleSheafAction X R a b ≫ h = freeModuleSheafAction X R a (b ≫ h) := by
  unfold freeModuleSheafAction
  rw [Category.assoc, ← leftUnitor_naturality, ← id_tensorHom,
    ← Category.assoc, freeModuleSheafPairing_postcomp, Category.comp_id]

theorem freeModuleSheafAction_add_left
    (a a' : (freeModuleSheafFunctor X R).obj P ⟶
      𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)))
    (b : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    freeModuleSheafAction X R (a + a') b =
      freeModuleSheafAction X R a b + freeModuleSheafAction X R a' b := by
  unfold freeModuleSheafAction
  rw [freeModuleSheafPairing_add_left, Preadditive.add_comp]

theorem freeModuleSheafAction_sub_right
    (a : (freeModuleSheafFunctor X R).obj P ⟶
      𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)))
    (b b' : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    freeModuleSheafAction X R a (b - b') =
      freeModuleSheafAction X R a b - freeModuleSheafAction X R a b' := by
  unfold freeModuleSheafAction
  rw [freeModuleSheafPairing_sub_right, Preadditive.sub_comp]

theorem freeModuleSheafAction_counit_left
    (b : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    freeModuleSheafAction X R (freeModuleSheafCounit X R P) b = b := by
  unfold freeModuleSheafAction
  rw [freeModuleSheafPairing_counit_left, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

theorem freeModuleSheafAction_counit_right
    (a : (freeModuleSheafFunctor X R).obj P ⟶
      𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) :
    freeModuleSheafAction X R a (freeModuleSheafCounit X R P) = a := by
  unfold freeModuleSheafAction
  rw [freeModuleSheafPairing_counit_right, Category.assoc, unitors_equal,
    Iso.inv_hom_id, Category.comp_id]

end EtaleCohomology
