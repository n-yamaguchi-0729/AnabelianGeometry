/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# Free module representables and actual covering augmentations

The free module sheaf on a representable corepresents actual module
sections. At a terminal object it is the original constant regular
coefficient sheaf. Sheaf descent proves that an actual covering map
induces the coequalizer augmentation of its free module Cech complex.
The arrows of this coequalizer are the original pullback projections.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type v) [CommRing R] [HasSheafify J (ModuleCat.{v} R)]

/-- The original sheafification of the free module on a representable. -/
abbrev freeModuleSheafYoneda : C ⥤ Sheaf J (ModuleCat.{v} R) :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free R) ⋙
    presheafToSheaf J (ModuleCat.{v} R)

/-- Free module representables corepresent actual sections. -/
def freeModuleSheafYonedaHomEquiv (V : C) (F : Sheaf J (ModuleCat.{v} R)) :
    ((freeModuleSheafYoneda J R).obj V ⟶ F) ≃ F.obj.obj (op V) :=
  ((sheafificationAdjunction J (ModuleCat.{v} R)).homEquiv
    (yoneda.obj V ⋙ ModuleCat.free R) F).trans
    ((((ModuleCat.adj R).whiskerRight Cᵒᵖ).homEquiv
      (yoneda.obj V) F.obj).trans yonedaEquiv)

/-- The section is evaluation on the actual identity generator. -/
theorem freeModuleSheafYonedaHomEquiv_apply (V : C)
    (F : Sheaf J (ModuleCat.{v} R)) (a : (freeModuleSheafYoneda J R).obj V ⟶ F) :
    freeModuleSheafYonedaHomEquiv J R V F a =
      (((sheafificationAdjunction J (ModuleCat.{v} R)).homEquiv
        (yoneda.obj V ⋙ ModuleCat.free R) F a).app (op V))
          (ModuleCat.freeMk (𝟙 V)) := rfl

/-- Evaluation retains the original coefficient map. -/
theorem freeModuleSheafYonedaHomEquiv_postcomp (V : C)
    {F G : Sheaf J (ModuleCat.{v} R)}
    (a : (freeModuleSheafYoneda J R).obj V ⟶ F) (η : F ⟶ G) :
    freeModuleSheafYonedaHomEquiv J R V G (a ≫ η) =
      η.hom.app (op V) (freeModuleSheafYonedaHomEquiv J R V F a) := by
  rw [freeModuleSheafYonedaHomEquiv_apply, Adjunction.homEquiv_naturality_right]
  rfl

/-- Evaluation retains the original restriction map of sections. -/
theorem freeModuleSheafYonedaHomEquiv_precomp {V W : C} (f : V ⟶ W)
    (F : Sheaf J (ModuleCat.{v} R)) (a : (freeModuleSheafYoneda J R).obj W ⟶ F) :
    freeModuleSheafYonedaHomEquiv J R V F ((freeModuleSheafYoneda J R).map f ≫ a) =
      F.obj.map f.op (freeModuleSheafYonedaHomEquiv J R W F a) := by
  let b : yoneda.obj W ⋙ ModuleCat.free R ⟶ F.obj :=
    (sheafificationAdjunction J (ModuleCat.{v} R)).homEquiv
      (yoneda.obj W ⋙ ModuleCat.free R) F a
  rw [freeModuleSheafYonedaHomEquiv_apply]
  change (((sheafificationAdjunction J (ModuleCat.{v} R)).homEquiv _ F
    ((presheafToSheaf J (ModuleCat.{v} R)).map
      (Functor.whiskerRight (yoneda.map f) (ModuleCat.free R)) ≫ a)).app (op V))
        (ModuleCat.freeMk (𝟙 V)) = _
  rw [Adjunction.homEquiv_naturality_left]
  change ((Functor.whiskerRight (yoneda.map f) (ModuleCat.free R) ≫ b).app
    (op V)) (ModuleCat.freeMk (𝟙 V)) =
    F.obj.map f.op (b.app (op W) (ModuleCat.freeMk (𝟙 W)))
  rw [NatTrans.comp_app, Functor.whiskerRight_app, ModuleCat.comp_apply,
    ModuleCat.free_map_apply, yoneda_map_app, TypeCat.ofHom_apply, Category.id_comp]
  have h := ConcreteCategory.congr_hom (b.naturality f.op)
    (ModuleCat.freeMk (𝟙 W))
  rw [Functor.comp_map, ModuleCat.comp_apply, ModuleCat.comp_apply,
    ModuleCat.free_map_apply, yoneda_obj_map, TypeCat.ofHom_apply] at h
  simpa only [Category.comp_id, Quiver.Hom.unop_op] using h

/-- At a terminal object, the actual free module representable is the
original constant regular module sheaf. -/
def freeModuleSheafYonedaTerminalIso {T : C} (hT : IsTerminal T) :
    (freeModuleSheafYoneda J R).obj T ≅
      (constantSheaf J (ModuleCat.{v} R)).obj (ModuleCat.of R R) := by
  let E : Sheaf J (ModuleCat.{v} R) ⥤ Type v :=
    sheafToPresheaf J (ModuleCat.{v} R) ⋙
      (evaluation _ _).obj (op T) ⋙ forget (ModuleCat.{v} R)
  let e : E.CorepresentableBy ((freeModuleSheafYoneda J R).obj T) :=
    { homEquiv := freeModuleSheafYonedaHomEquiv J R T _
      homEquiv_comp := fun η a => freeModuleSheafYonedaHomEquiv_postcomp J R T a η }
  let e' : E.CorepresentableBy
      ((constantSheaf J (ModuleCat.{v} R)).obj (ModuleCat.of R R)) :=
    { homEquiv := fun {F} =>
        ((constantSheafAdj J (ModuleCat.{v} R) hT).homEquiv _ F).trans
          (ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf R R _).toEquiv)
      homEquiv_comp := by
        intro F G η a
        change (((constantSheafAdj J (ModuleCat.{v} R) hT).homEquiv _ G
          (a ≫ η)).hom) 1 = _
        rw [Adjunction.homEquiv_naturality_right]
        rfl }
  exact e.uniqueUpToIso e'

/-- The actual covering augmentation and its two original relation arrows. -/
abbrev freeModuleSheafYonedaCoverCofork {V W : C} (f : V ⟶ W)
    [HasPullback f f] :
    Cofork ((freeModuleSheafYoneda J R).map (pullback.fst f f))
      ((freeModuleSheafYoneda J R).map (pullback.snd f f)) :=
  Cofork.ofπ ((freeModuleSheafYoneda J R).map f) (by
    rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition])

/-- Actual sheaf descent gives the original cover augmentation its
coequalizer universal property in module sheaves. -/
def freeModuleSheafYonedaCoverIsColimit {V W : C} (f : V ⟶ W)
    [HasPullback f f] (hf : Sieve.generate (Presieve.singleton f) ∈ J W) :
    IsColimit (freeModuleSheafYonedaCoverCofork J R f) := by
  apply Cofork.IsColimit.ofExistsUnique
  intro s
  let F : Sheaf J (ModuleCat.{v} R) := s.pt
  let a : (freeModuleSheafYoneda J R).obj V ⟶ F := s.π
  have hF : Presieve.IsSheafFor (F.obj ⋙ forget (ModuleCat.{v} R))
      (Presieve.singleton f) :=
    (Presieve.isSheafFor_iff_generate _).mpr
      ((isSheaf_iff_isSheaf_of_type J _).mp
        (Presheaf.isSheaf_comp_of_isSheaf J F.obj
          (forget (ModuleCat.{v} R)) F.property) _ hf)
  have ha : ∀ {Z : C} (p q : Z ⟶ V), p ≫ f = q ≫ f →
      (freeModuleSheafYoneda J R).map p ≫ a =
        (freeModuleSheafYoneda J R).map q ≫ a := by
    intro Z p q hpq
    let l : Z ⟶ pullback f f := pullback.lift p q hpq
    calc
      (freeModuleSheafYoneda J R).map p ≫ a =
          (freeModuleSheafYoneda J R).map l ≫
            (freeModuleSheafYoneda J R).map (pullback.fst f f) ≫ a := by
        rw [← Category.assoc, ← Functor.map_comp, pullback.lift_fst]
      _ = (freeModuleSheafYoneda J R).map l ≫
            (freeModuleSheafYoneda J R).map (pullback.snd f f) ≫ a := by
        rw [s.condition]
      _ = (freeModuleSheafYoneda J R).map q ≫ a := by
        rw [← Category.assoc, ← Functor.map_comp, pullback.lift_snd]
  obtain ⟨t, ht, huniq⟩ := (Presieve.isSheafFor_singleton.mp hF)
    (freeModuleSheafYonedaHomEquiv J R V F a) (by
      intro Z p q hpq
      change F.obj.map p.op _ = F.obj.map q.op _
      rw [← freeModuleSheafYonedaHomEquiv_precomp,
        ← freeModuleSheafYonedaHomEquiv_precomp, ha p q hpq])
  let d : (freeModuleSheafYoneda J R).obj W ⟶ F :=
    (freeModuleSheafYonedaHomEquiv J R W F).symm t
  refine ⟨d, ?_, ?_⟩
  · apply (freeModuleSheafYonedaHomEquiv J R V F).injective
    change freeModuleSheafYonedaHomEquiv J R V F
      ((freeModuleSheafYoneda J R).map f ≫ d) = _
    rw [freeModuleSheafYonedaHomEquiv_precomp]
    exact (congrArg (F.obj.map f.op)
      ((freeModuleSheafYonedaHomEquiv J R W F).apply_symm_apply t)).trans ht
  · intro d' hd'
    apply (freeModuleSheafYonedaHomEquiv J R W F).injective
    change _ = freeModuleSheafYonedaHomEquiv J R W F
      ((freeModuleSheafYonedaHomEquiv J R W F).symm t)
    rw [Equiv.apply_symm_apply]
    apply huniq
    change F.obj.map f.op (freeModuleSheafYonedaHomEquiv J R W F d') = _
    rw [← freeModuleSheafYonedaHomEquiv_precomp]
    exact congrArg (freeModuleSheafYonedaHomEquiv J R V F) hd'

/-- An actual covering map gives an epimorphism of the actual free
module sheaves, independently of the coefficient characteristic. -/
theorem freeModuleSheafYoneda_map_epi_of_cover {V W : C} (f : V ⟶ W)
    [HasPullback f f] (hf : Sieve.generate (Presieve.singleton f) ∈ J W) :
    Epi ((freeModuleSheafYoneda J R).map f) :=
  epi_of_isColimit_cofork (freeModuleSheafYonedaCoverIsColimit J R f hf)

end EtaleCohomology
