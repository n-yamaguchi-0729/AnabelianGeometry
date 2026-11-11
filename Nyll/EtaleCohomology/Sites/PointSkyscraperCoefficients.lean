/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Point skyscrapers and coefficient functors

A coefficient functor preserving the relevant products commutes with the
actual native point skyscraper. If its functor on sheaves also preserves
products, it commutes with actual small families of skyscrapers. Both
comparisons are constructed from the canonical product comparison maps.
-/

@[expose] public section

noncomputable section

universe u v w uA uB vA vB

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type uA} [Category.{vA} A] [HasProducts.{w} A]
  {B : Type uB} [Category.{vB} B] [HasProducts.{w} B]
  (Φ : Point.{w} J) (F : A ⥤ B) [J.HasSheafCompose F]
  [PreservesLimitsOfSize.{w, w} F]

/-- Changing coefficients commutes with the actual point skyscraper through
preservation of its sectionwise products. -/
def skyscraperSheafComposeIso (M : A) :
    (sheafCompose J F).obj (Φ.skyscraperSheafFunctor.obj M) ≅
      Φ.skyscraperSheafFunctor.obj (F.obj M) :=
  (sheafToPresheaf J B).preimageIso
    (NatIso.ofComponents
      (fun U => PreservesProduct.iso F (fun _ : Φ.fiber.obj U.unop => M))
      (by
        intro U V f
        change F.map (Limits.Pi.map' (Φ.fiber.map f.unop) (fun _ => 𝟙 M)) ≫
            piComparison F (fun _ : Φ.fiber.obj V.unop => M) =
          piComparison F (fun _ : Φ.fiber.obj U.unop => M) ≫
            Limits.Pi.map' (Φ.fiber.map f.unop) (fun _ => 𝟙 (F.obj M))
        apply Limits.Pi.hom_ext
        intro x
        rw [Category.assoc, piComparison_comp_π, ← F.map_comp,
          Limits.Pi.map'_comp_π, Category.comp_id, Category.assoc,
          Limits.Pi.map'_comp_π, Category.comp_id, piComparison_comp_π]))

end CategoryTheory.GrothendieckTopology.Point
