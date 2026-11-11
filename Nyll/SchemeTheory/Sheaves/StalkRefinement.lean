/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Ring-stalk comparisons from pointed refinements

A map of ring presheaves induces a bijection on a stalk when every
pointed neighborhood has a further pointed refinement on which the
section map is bijective. No comparison of stalks is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

universe u v

variable {C : Type v} [Category.{u} C] [LocallySmall.{u} C]
  {J : GrothendieckTopology C} (Φ : J.Point.{u})
  {P Q : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Taking the actual stalk of abelian presheaves preserves addition of maps. -/
instance abelianPresheafFiber_additive :
    (Φ.presheafFiber (A := AddCommGrpCat.{u})).Additive where
  map_add {X Y} f g := by
    apply Φ.presheafFiber_hom_ext
    intro W w
    rw [Preadditive.comp_add, Φ.toPresheafFiber_naturality,
      Φ.toPresheafFiber_naturality, Φ.toPresheafFiber_naturality]
    exact Preadditive.add_comp (C := AddCommGrpCat.{u})
      (X.obj (op W)) (Y.obj (op W)) (Φ.presheafFiber.obj Y)
      (f.app (op W)) (g.app (op W)) (Φ.toPresheafFiber W w Y)

/-- Taking the actual stalk of abelian sheaves preserves addition of maps. -/
instance abelianSheafFiber_additive :
    (Φ.sheafFiber (A := AddCommGrpCat.{u})).Additive where
  map_add {X Y} f g := by
    change Φ.presheafFiber.map (f.hom + g.hom) =
      Φ.presheafFiber.map f.hom + Φ.presheafFiber.map g.hom
    exact (Φ.presheafFiber (A := AddCommGrpCat.{u})).map_add

/-- A sectionwise bijective comparison on cofinal pointed refinements
induces a bijection on the actual ring stalk. -/
theorem ringPresheafFiber_map_bijective_of_refinements (η : P ⟶ Q)
    (href : ∀ (W : C) (t : Φ.fiber.obj W),
      ∃ (V : C) (g : V ⟶ W) (v : Φ.fiber.obj V),
        Φ.fiber.map g v = t ∧ Function.Bijective (η.app (op V))) :
    Function.Bijective ((Φ.presheafFiber (A := CommRingCat.{u})).map η) := by
  constructor
  · intro x y hxy
    obtain ⟨W, t, a, b, rfl, rfl⟩ :=
      Φ.toPresheafFiber_jointly_surjective₂ (P := P) x y
    have ha := ConcreteCategory.congr_hom
      (Φ.toPresheafFiber_naturality η W t) a
    have hb := ConcreteCategory.congr_hom
      (Φ.toPresheafFiber_naturality η W t) b
    have hQ : Φ.toPresheafFiber W t Q (η.app (op W) a) =
        Φ.toPresheafFiber W t Q (η.app (op W) b) :=
      ha.symm.trans (hxy.trans hb)
    obtain ⟨U, g, u, hgu, hU⟩ :=
      (Φ.toPresheafFiber_eq_iff' (P := Q) W t _ _).mp hQ
    have hηU : η.app (op U) (P.map g.op a) =
        η.app (op U) (P.map g.op b) :=
      (ConcreteCategory.congr_hom (η.naturality g.op) a).trans
        (hU.trans (ConcreteCategory.congr_hom (η.naturality g.op) b).symm)
    obtain ⟨V, h, v, hhv, hbij⟩ := href U u
    have hηV : η.app (op V) (P.map h.op (P.map g.op a)) =
        η.app (op V) (P.map h.op (P.map g.op b)) :=
      (ConcreteCategory.congr_hom (η.naturality h.op) (P.map g.op a)).trans
        ((congrArg (Q.map h.op) hηU).trans
          (ConcreteCategory.congr_hom (η.naturality h.op) (P.map g.op b)).symm)
    have hV := hbij.1 hηV
    apply (Φ.toPresheafFiber_eq_iff' (P := P) W t a b).mpr
    refine ⟨V, h ≫ g, v, ?_, ?_⟩
    · rw [Functor.map_comp]
      change Φ.fiber.map g (Φ.fiber.map h v) = t
      rw [hhv, hgu]
    · change P.map ((h ≫ g).op) a = P.map ((h ≫ g).op) b
      rw [op_comp, Functor.map_comp]
      exact hV
  · intro z
    obtain ⟨W, t, a, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := Q) z
    obtain ⟨V, g, v, hgv, hbij⟩ := href W t
    obtain ⟨b, hb⟩ := hbij.2 (Q.map g.op a)
    refine ⟨Φ.toPresheafFiber V v P b, ?_⟩
    have hη := ConcreteCategory.congr_hom
      (Φ.toPresheafFiber_naturality η V v) b
    have hg := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w g v Q) a
    rw [hgv] at hg
    exact hη.trans ((congrArg (Φ.toPresheafFiber V v Q) hb).trans hg)

end CategoryTheory.GrothendieckTopology.Point
