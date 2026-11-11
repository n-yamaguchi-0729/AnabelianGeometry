/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCoalgebra
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Classical.ModuleExtCohomology
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# The same actual cochains with free abelian and free module sources

The two original free adjunctions identify their sheaf cochains with
the same maps of underlying type-valued presheaves. The resulting
additive equivalence retains the value on every generator, source
maps, and coefficient maps. Its actual source morphism is the
canonical free abelian to free module map followed by forgetting the
module structure. No module structure on an abelian extension is
assumed or introduced.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- The actual free abelian sheaf on an arbitrary presheaf of sets. -/
abbrev freeAbelianSheafFunctor :
    (X.Etaleᵒᵖ ⥤ Type u) ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- The actual two module adjunctions, before evaluating a
representable or identifying any locally constant section. -/
def freeModuleSheafHomEquiv (P : X.Etaleᵒᵖ ⥤ Type u)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    ((freeModuleSheafFunctor X R).obj P ⟶ F) ≃
      (P ⟶ F.obj ⋙ forget (ModuleCat.{u} R)) :=
  ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u} R)).homEquiv
    (P ⋙ ModuleCat.free R) F).trans
    (((ModuleCat.adj R).whiskerRight X.Etaleᵒᵖ).homEquiv P F.obj)

/-- The actual two abelian adjunctions on the same presheaf of sets. -/
def freeAbelianSheafHomEquiv (P : X.Etaleᵒᵖ ⥤ Type u)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ((freeAbelianSheafFunctor X).obj P ⟶ F) ≃
      (P ⟶ F.obj ⋙ forget AddCommGrpCat.{u}) :=
  ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u}).homEquiv
    (P ⋙ AddCommGrpCat.free) F).trans
    ((AddCommGrpCat.adj.whiskerRight X.Etaleᵒᵖ).homEquiv P F.obj)

theorem freeModuleSheafHomEquiv_precomp
    {P Q : X.Etaleᵒᵖ ⥤ Type u} (η : P ⟶ Q)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (a : (freeModuleSheafFunctor X R).obj Q ⟶ F) :
    freeModuleSheafHomEquiv X R P F ((freeModuleSheafFunctor X R).map η ≫ a) =
      η ≫ freeModuleSheafHomEquiv X R Q F a := by
  change ((ModuleCat.adj R).whiskerRight X.Etaleᵒᵖ).homEquiv P F.obj
    (((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u} R)).homEquiv _ F)
      ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
        (Functor.whiskerRight η (ModuleCat.free R)) ≫ a)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact ((ModuleCat.adj R).whiskerRight X.Etaleᵒᵖ).homEquiv_naturality_left η _

theorem freeAbelianSheafHomEquiv_precomp
    {P Q : X.Etaleᵒᵖ ⥤ Type u} (η : P ⟶ Q)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : (freeAbelianSheafFunctor X).obj Q ⟶ F) :
    freeAbelianSheafHomEquiv X P F ((freeAbelianSheafFunctor X).map η ≫ a) =
      η ≫ freeAbelianSheafHomEquiv X Q F a := by
  change (AddCommGrpCat.adj.whiskerRight X.Etaleᵒᵖ).homEquiv P F.obj
    (((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u}).homEquiv _ F)
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (Functor.whiskerRight η AddCommGrpCat.free) ≫ a)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact (AddCommGrpCat.adj.whiskerRight X.Etaleᵒᵖ).homEquiv_naturality_left η _

theorem freeModuleSheafHomEquiv_postcomp
    (P : X.Etaleᵒᵖ ⥤ Type u) {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (a : (freeModuleSheafFunctor X R).obj P ⟶ F) (k : F ⟶ G) :
    freeModuleSheafHomEquiv X R P G (a ≫ k) =
      freeModuleSheafHomEquiv X R P F a ≫
        Functor.whiskerRight k.hom (forget (ModuleCat.{u} R)) := by
  change ((ModuleCat.adj R).whiskerRight X.Etaleᵒᵖ).homEquiv P G.obj
    (((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u} R)).homEquiv _ G)
      (a ≫ k)) = _
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  rfl

theorem freeAbelianSheafHomEquiv_postcomp
    (P : X.Etaleᵒᵖ ⥤ Type u) {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (a : (freeAbelianSheafFunctor X).obj P ⟶ F) (k : F ⟶ G) :
    freeAbelianSheafHomEquiv X P G (a ≫ k) =
      freeAbelianSheafHomEquiv X P F a ≫
        Functor.whiskerRight k.hom (forget AddCommGrpCat.{u}) := by
  change (AddCommGrpCat.adj.whiskerRight X.Etaleᵒᵖ).homEquiv P G.obj
    (((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u}).homEquiv _ G)
      (a ≫ k)) = _
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  rfl

/-- Module cochains and abelian cochains give the same actual map
on every original generator. -/
def freeModuleSheafUnderlyingHomEquiv (P : X.Etaleᵒᵖ ⥤ Type u)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    ((freeModuleSheafFunctor X R).obj P ⟶ F) ≃
      ((freeAbelianSheafFunctor X).obj P ⟶
        (Classical.forgetCoefficients.{u + 1, u, u, u}).obj F) :=
  (freeModuleSheafHomEquiv X R P F).trans
    (freeAbelianSheafHomEquiv X P
      ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj F)).symm

theorem freeModuleSheafUnderlyingHomEquiv_sections
    (P : X.Etaleᵒᵖ ⥤ Type u) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (a : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    freeAbelianSheafHomEquiv X P ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj F)
        (freeModuleSheafUnderlyingHomEquiv X R P F a) =
      freeModuleSheafHomEquiv X R P F a :=
  (freeAbelianSheafHomEquiv X P
    ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj F)).apply_symm_apply _

/-- In particular the comparison retains the literal values on
the original free abelian and free module generators. -/
theorem freeModuleSheafUnderlyingHomEquiv_generator
    (P : X.Etaleᵒᵖ ⥤ Type u) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (a : (freeModuleSheafFunctor X R).obj P ⟶ F) (V : X.Etaleᵒᵖ) (x : P.obj V) :
    (((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u}).homEquiv _
      ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj F)
      (freeModuleSheafUnderlyingHomEquiv X R P F a)).app V)
        (FreeAbelianGroup.of x) =
      (((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u} R)).homEquiv _ F a).app V)
        (ModuleCat.freeMk x) :=
  congrArg (fun η => η.app V x) (freeModuleSheafUnderlyingHomEquiv_sections X R P F a)

theorem freeModuleSheafUnderlyingHomEquiv_precomp
    {P Q : X.Etaleᵒᵖ ⥤ Type u} (η : P ⟶ Q)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (a : (freeModuleSheafFunctor X R).obj Q ⟶ F) :
    freeModuleSheafUnderlyingHomEquiv X R P F ((freeModuleSheafFunctor X R).map η ≫ a) =
      (freeAbelianSheafFunctor X).map η ≫ freeModuleSheafUnderlyingHomEquiv X R Q F a := by
  apply (freeAbelianSheafHomEquiv X P
    ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj F)).injective
  rw [freeModuleSheafUnderlyingHomEquiv_sections, freeAbelianSheafHomEquiv_precomp,
    freeModuleSheafUnderlyingHomEquiv_sections, freeModuleSheafHomEquiv_precomp]
  rfl

theorem freeModuleSheafUnderlyingHomEquiv_postcomp
    (P : X.Etaleᵒᵖ ⥤ Type u) {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (a : (freeModuleSheafFunctor X R).obj P ⟶ F) (k : F ⟶ G) :
    freeModuleSheafUnderlyingHomEquiv X R P G (a ≫ k) =
      freeModuleSheafUnderlyingHomEquiv X R P F a ≫
        (Classical.forgetCoefficients.{u + 1, u, u, u}).map k := by
  apply (freeAbelianSheafHomEquiv X P
    ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj G)).injective
  rw [freeModuleSheafUnderlyingHomEquiv_sections, freeAbelianSheafHomEquiv_postcomp,
    freeModuleSheafUnderlyingHomEquiv_sections, freeModuleSheafHomEquiv_postcomp]
  rfl

/-- The actual source map of the cochain comparison. -/
def freeModuleSheafIntegerMap (P : X.Etaleᵒᵖ ⥤ Type u) :
    (freeAbelianSheafFunctor X).obj P ⟶
      (Classical.forgetCoefficients.{u + 1, u, u, u}).obj ((freeModuleSheafFunctor X R).obj P) :=
  freeModuleSheafUnderlyingHomEquiv X R P ((freeModuleSheafFunctor X R).obj P) (𝟙 _)

/-- Every cochain comparison uses this same actual source map. -/
theorem freeModuleSheafUnderlyingHomEquiv_eq
    (P : X.Etaleᵒᵖ ⥤ Type u) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (a : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    freeModuleSheafUnderlyingHomEquiv X R P F a =
      freeModuleSheafIntegerMap X R P ≫
        (Classical.forgetCoefficients.{u + 1, u, u, u}).map a := by
  exact ((congrArg (freeModuleSheafUnderlyingHomEquiv X R P F)
    (Category.id_comp a)).symm).trans
      (freeModuleSheafUnderlyingHomEquiv_postcomp X R P (𝟙 _) a)

/-- The source map commutes with the actual free maps of presheaves. -/
theorem freeModuleSheafIntegerMap_naturality
    {P Q : X.Etaleᵒᵖ ⥤ Type u} (η : P ⟶ Q) :
    (freeAbelianSheafFunctor X).map η ≫ freeModuleSheafIntegerMap X R Q =
      freeModuleSheafIntegerMap X R P ≫
        (Classical.forgetCoefficients.{u + 1, u, u, u}).map
          ((freeModuleSheafFunctor X R).map η) := by
  calc
    _ = freeModuleSheafUnderlyingHomEquiv X R P ((freeModuleSheafFunctor X R).obj Q)
        ((freeModuleSheafFunctor X R).map η ≫ 𝟙 _) :=
      (freeModuleSheafUnderlyingHomEquiv_precomp X R η _ (𝟙 _)).symm
    _ = freeModuleSheafUnderlyingHomEquiv X R P ((freeModuleSheafFunctor X R).obj Q)
        ((freeModuleSheafFunctor X R).map η) := by rw [Category.comp_id]
    _ = _ := freeModuleSheafUnderlyingHomEquiv_eq X R P _ _

/-- The same cochain comparison preserves the original addition. -/
def freeModuleSheafUnderlyingHomAddEquiv (P : X.Etaleᵒᵖ ⥤ Type u)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    ((freeModuleSheafFunctor X R).obj P ⟶ F) ≃+
      ((freeAbelianSheafFunctor X).obj P ⟶
        (Classical.forgetCoefficients.{u + 1, u, u, u}).obj F) where
  toEquiv := freeModuleSheafUnderlyingHomEquiv X R P F
  map_add' a b := by
    let U : Sheaf X.smallEtaleTopology (ModuleCat.{u} R) ⥤
        Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
      Classical.forgetCoefficients.{u + 1, u, u, u}
    have hmap : U.map (a + b) = U.map a + U.map b := U.map_add
    exact (freeModuleSheafUnderlyingHomEquiv_eq X R P F (a + b)).trans
      ((congrArg (fun k => freeModuleSheafIntegerMap X R P ≫ k) hmap).trans
        ((Preadditive.comp_add _ _ _ (freeModuleSheafIntegerMap X R P)
          (U.map a) (U.map b)).trans
            (congrArg₂ (fun k l => k + l)
              (freeModuleSheafUnderlyingHomEquiv_eq X R P F a).symm
              (freeModuleSheafUnderlyingHomEquiv_eq X R P F b).symm)))

end EtaleCohomology
