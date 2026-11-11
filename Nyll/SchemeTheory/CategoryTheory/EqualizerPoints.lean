/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # Points of the actual fixed scheme over a base -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace AlgebraicGeometry

universe u

/-- Points of the actual equalizer are exactly the original points fixed by
the endomorphism, with the given structure morphism retained. -/
def schemeHomOverEqualizerEquivFixed {B T X : Scheme.{u}}
    (t : T ⟶ B) (f : X ⟶ B) (v : X ⟶ X) :
    SchemeHomOver t (equalizer.ι v (𝟙 X) ≫ f) ≃
      {x : SchemeHomOver t f // x.val ≫ v = x.val} where
  toFun p := ⟨⟨p.val ≫ equalizer.ι v (𝟙 X), by
      rw [Category.assoc]
      exact p.property⟩, by
    rw [Category.assoc, equalizer.condition, Category.comp_id]⟩
  invFun x := ⟨equalizer.lift x.val.val
    (x.property.trans (Category.comp_id x.val.val).symm), by
      rw [← Category.assoc, equalizer.lift_ι]
      exact x.val.property⟩
  left_inv p := by
    apply Subtype.ext
    apply equalizer.hom_ext
    exact equalizer.lift_ι _ _
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact equalizer.lift_ι _ _

/-- The point equivalence is induced by the original equalizer immersion. -/
theorem schemeHomOverEqualizerEquivFixed_apply
    {B T X : Scheme.{u}} (t : T ⟶ B) (f : X ⟶ B) (v : X ⟶ X)
    (p : SchemeHomOver t (equalizer.ι v (𝟙 X) ≫ f)) :
    (schemeHomOverEqualizerEquivFixed t f v p).val.val =
      p.val ≫ equalizer.ι v (𝟙 X) := rfl

end AlgebraicGeometry
