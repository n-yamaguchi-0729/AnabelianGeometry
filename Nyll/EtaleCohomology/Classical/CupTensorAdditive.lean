/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupTensorSheaves
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Additivity of the original sheaf tensor

The actual comparison between sheaf tensor and sheafification of the
pointwise tensor is natural in both variables. It identifies each
original sheaf tensor functor with an additive composite of the original
forgetful functor, pointwise module tensor, and sheafification.

The resulting scoped monoidal preadditive structure uses the original
abelian addition on sheaf morphisms. It is the input needed to form
tensor total complexes and their signed shift comparisons.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

namespace EtaleCohomology.ModuleTensor

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- The actual tensor-sheafification comparison is natural in both
original sheaf morphisms. -/
theorem tensorSheafificationIso_naturality
    {F F' G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (f : F ⟶ F') (g : G ⟶ G') :
    (f ⊗ₘ g) ≫ (tensorSheafificationIso X R F' G').hom =
      (tensorSheafificationIso X R F G).hom ≫
        (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map (f.hom ⊗ₘ g.hom) := by
  let L := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)
  let ε := asIso (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u} R)).counit
  change (f ⊗ₘ g) ≫ ((ε.inv.app F' ⊗ₘ ε.inv.app G') ≫
      Functor.LaxMonoidal.μ L F'.obj G'.obj) =
    ((ε.inv.app F ⊗ₘ ε.inv.app G) ≫ Functor.LaxMonoidal.μ L F.obj G.obj) ≫
      L.map (f.hom ⊗ₘ g.hom)
  have hf : f ≫ ε.inv.app F' = ε.inv.app F ≫ L.map f.hom :=
    ε.inv.naturality f
  have hg : g ≫ ε.inv.app G' = ε.inv.app G ≫ L.map g.hom :=
    ε.inv.naturality g
  have hμ : (L.map f.hom ⊗ₘ L.map g.hom) ≫ Functor.LaxMonoidal.μ L F'.obj G'.obj =
      Functor.LaxMonoidal.μ L F.obj G.obj ≫ L.map (f.hom ⊗ₘ g.hom) :=
    Functor.LaxMonoidal.μ_natural L f.hom g.hom
  calc
    _ = ((f ≫ ε.inv.app F') ⊗ₘ (g ≫ ε.inv.app G')) ≫
        Functor.LaxMonoidal.μ L F'.obj G'.obj := by
      rw [← Category.assoc, tensorHom_comp_tensorHom]
    _ = ((ε.inv.app F ≫ L.map f.hom) ⊗ₘ (ε.inv.app G ≫ L.map g.hom)) ≫
        Functor.LaxMonoidal.μ L F'.obj G'.obj := by
      exact congrArg₂
        (fun (a : F ⟶ L.obj F'.obj) (b : G ⟶ L.obj G'.obj) =>
          (a ⊗ₘ b) ≫ Functor.LaxMonoidal.μ L F'.obj G'.obj) hf hg
    _ = (ε.inv.app F ⊗ₘ ε.inv.app G) ≫
        ((L.map f.hom ⊗ₘ L.map g.hom) ≫ Functor.LaxMonoidal.μ L F'.obj G'.obj) := by
      rw [← tensorHom_comp_tensorHom, Category.assoc]
    _ = _ :=
      (congrArg
        (fun h : L.obj F.obj ⊗ L.obj G.obj ⟶ L.obj (F'.obj ⊗ G'.obj) =>
          (ε.inv.app F ⊗ₘ ε.inv.app G) ≫ h) hμ).trans
        (Category.assoc (ε.inv.app F ⊗ₘ ε.inv.app G)
          (Functor.LaxMonoidal.μ L F.obj G.obj) (L.map (f.hom ⊗ₘ g.hom))).symm

/-- The original left sheaf tensor functor is the sheafification of
the pointwise tensor of the original underlying presheaves. -/
def tensorLeftSheafificationIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    tensorLeft F ≅ sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u} R) ⋙
      tensorLeft F.obj ⋙ presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
  NatIso.ofComponents (fun G => tensorSheafificationIso X R F G) (by
    intro G H g
    change (F ◁ g) ≫ (tensorSheafificationIso X R F H).hom =
      (tensorSheafificationIso X R F G).hom ≫
        (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map (F.obj ◁ g.hom)
    have hid : (𝟙 F : F ⟶ F).hom = 𝟙 F.obj := rfl
    have ht : (𝟙 F : F ⟶ F).hom ⊗ₘ g.hom = F.obj ◁ g.hom :=
      (congrArg (fun a : F.obj ⟶ F.obj => a ⊗ₘ g.hom) hid).trans
        (id_tensorHom F.obj g.hom)
    have hl : (F ◁ g) ≫ (tensorSheafificationIso X R F H).hom =
        (𝟙 F ⊗ₘ g) ≫ (tensorSheafificationIso X R F H).hom :=
      congrArg (fun a : F ⊗ G ⟶ F ⊗ H =>
        a ≫ (tensorSheafificationIso X R F H).hom) (id_tensorHom F g).symm
    exact hl.trans ((tensorSheafificationIso_naturality X R (𝟙 F) g).trans
      (congrArg (fun a : F.obj ⊗ G.obj ⟶ F.obj ⊗ H.obj =>
        (tensorSheafificationIso X R F G).hom ≫
          (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map a) ht)))

/-- The original right sheaf tensor functor has the corresponding
pointwise sheafification description. -/
def tensorRightSheafificationIso
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    tensorRight G ≅ sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u} R) ⋙
      tensorRight G.obj ⋙ presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
  NatIso.ofComponents (fun F => tensorSheafificationIso X R F G) (by
    intro F H f
    change (f ▷ G) ≫ (tensorSheafificationIso X R H G).hom =
      (tensorSheafificationIso X R F G).hom ≫
        (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map (f.hom ▷ G.obj)
    have hid : (𝟙 G : G ⟶ G).hom = 𝟙 G.obj := rfl
    have ht : f.hom ⊗ₘ (𝟙 G : G ⟶ G).hom = f.hom ▷ G.obj :=
      (congrArg (fun a : G.obj ⟶ G.obj => f.hom ⊗ₘ a) hid).trans
        (tensorHom_id f.hom G.obj)
    have hl : (f ▷ G) ≫ (tensorSheafificationIso X R H G).hom =
        (f ⊗ₘ 𝟙 G) ≫ (tensorSheafificationIso X R H G).hom :=
      congrArg (fun a : F ⊗ G ⟶ H ⊗ G =>
        a ≫ (tensorSheafificationIso X R H G).hom) (tensorHom_id f G).symm
    exact hl.trans ((tensorSheafificationIso_naturality X R f (𝟙 G)).trans
      (congrArg (fun a : F.obj ⊗ G.obj ⟶ H.obj ⊗ G.obj =>
        (tensorSheafificationIso X R F G).hom ≫
          (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map a) ht)))

private theorem presheafTensorLeft_additive (F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} R) :
    (tensorLeft F).Additive := by
  constructor
  intro G H f g
  apply NatTrans.ext
  funext U
  change F.obj U ◁ (f.app U + g.app U) = F.obj U ◁ f.app U + F.obj U ◁ g.app U
  exact MonoidalPreadditive.whiskerLeft_add _ _

private theorem presheafTensorRight_additive (G : X.Etaleᵒᵖ ⥤ ModuleCat.{u} R) :
    (tensorRight G).Additive := by
  constructor
  intro F H f g
  apply NatTrans.ext
  funext U
  change (f.app U + g.app U) ▷ G.obj U = f.app U ▷ G.obj U + g.app U ▷ G.obj U
  exact MonoidalPreadditive.add_whiskerRight _ _

private theorem sheafTensorLeft_additive
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (tensorLeft F).Additive := by
  have : (tensorLeft F.obj).Additive := presheafTensorLeft_additive X R F.obj
  exact Functor.additive_of_iso (tensorLeftSheafificationIso X R F).symm

private theorem sheafTensorRight_additive
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (tensorRight G).Additive := by
  have : (tensorRight G.obj).Additive := presheafTensorRight_additive X R G.obj
  exact Functor.additive_of_iso (tensorRightSheafificationIso X R G).symm

/-- The actual sheafified tensor respects the original addition and
zero on module-sheaf morphisms in each variable. -/
scoped instance monoidalPreadditive :
    MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) where
  whiskerLeft_zero {F G H} := by
    have : (tensorLeft F).Additive := sheafTensorLeft_additive X R F
    exact (tensorLeft F).mapAddHom.map_zero
  zero_whiskerRight {G F H} := by
    have : (tensorRight G).Additive := sheafTensorRight_additive X R G
    exact (tensorRight G).mapAddHom.map_zero
  whiskerLeft_add {F G H} f g := by
    have : (tensorLeft F).Additive := sheafTensorLeft_additive X R F
    exact (tensorLeft F).map_add
  add_whiskerRight {G F H} f g := by
    have : (tensorRight G).Additive := sheafTensorRight_additive X R G
    exact (tensorRight G).map_add

end EtaleCohomology.ModuleTensor
