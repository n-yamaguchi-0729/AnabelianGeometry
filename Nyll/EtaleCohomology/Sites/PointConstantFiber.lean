/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Actual fibers of constant sheaves

A point has exactly one element over a terminal object of the site. Consequently
terminal sections of its native skyscraper recover the coefficient object.
Uniqueness of left adjoints then identifies the actual fiber of a constant
sheaf with its original coefficient object. This applies to arbitrary
coefficients for which the native constructions exist.
-/

@[expose] public section

noncomputable section

universe u v w uA vA

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C} (Φ : Point.{w} J)
  (A : Type uA) [Category.{vA} A] [HasProducts.{w} A]
  {T : C} (hT : IsTerminal T)

/-- Sections at the actual terminal object recover the coefficient of a
native point skyscraper through the singleton product comparison. -/
def skyscraperSheafFunctorSectionsIso :
    Φ.skyscraperSheafFunctor (A := A) ⋙ (sheafSections J A).obj (op T) ≅ 𝟭 A := by
  let : Unique (Φ.fiber.obj T) := Φ.uniqueFiberObj T hT
  exact NatIso.ofComponents
    (fun M => productUniqueIso (fun _ : Φ.fiber.obj T => M)) (by
      intro M N f
      change Limits.Pi.map (fun _ : Φ.fiber.obj T => f) ≫
          (productUniqueIso (fun _ : Φ.fiber.obj T => N)).hom =
        (productUniqueIso (fun _ : Φ.fiber.obj T => M)).hom ≫ f
      simp only [productUniqueIso_hom, Limits.Pi.map_π])

variable [HasColimitsOfSize.{w, w} A] [HasWeakSheafify J A]

/-- The actual point fiber of a constant sheaf is its original coefficient,
by the native skyscraper adjunction and constant-sheaf adjunction. -/
def constantSheafCompFiberIso :
    constantSheaf J A ⋙ Φ.sheafFiber ≅ 𝟭 A :=
  (((constantSheafAdj J A hT).comp Φ.skyscraperSheafAdjunction).ofNatIsoRight
    (Φ.skyscraperSheafFunctorSectionsIso A hT)).leftAdjointUniq (Adjunction.id)

/-- The original constant-section unit followed by the original germ is
the inverse of the existing constant-fiber comparison. -/
theorem constantSheaf_unit_germ_comp_fiberIso (M : A) (t : Φ.fiber.obj T) :
    (constantSheafAdj J A hT).unit.app M ≫
        Φ.toPresheafFiber T t ((constantSheaf J A).obj M).obj ≫
        (Φ.constantSheafCompFiberIso A hT).hom.app M = 𝟙 M := by
  let : Unique (Φ.fiber.obj T) := Φ.uniqueFiberObj T hT
  let adj := ((constantSheafAdj J A hT).comp Φ.skyscraperSheafAdjunction).ofNatIsoRight
    (Φ.skyscraperSheafFunctorSectionsIso A hT)
  let e := Φ.constantSheafCompFiberIso A hT
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app adj (Adjunction.id) M
  change adj.homEquiv M M (e.hom.app M) = 𝟙 M at h
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv,
    Equiv.trans_apply, Adjunction.homEquiv_unit] at h
  let F : Sheaf J A := (constantSheaf J A).obj M
  let f : Φ.sheafFiber.obj F ⟶ M := e.hom.app M
  let η : F ⟶ Φ.skyscraperSheaf M := Φ.skyscraperSheafAdjunction.homEquiv F M f
  let δ := η.hom.app (op T)
  let τ := (Φ.skyscraperSheafFunctorSectionsIso A hT).hom.app M
  let unit := (constantSheafAdj J A hT).unit.app M
  have hδ : δ = (Φ.skyscraperPresheafHomEquiv f).app (op T) :=
    congrArg (fun z : F.obj ⟶ Φ.skyscraperPresheaf M => z.app (op T))
      (Φ.skyscraperSheafAdjunction_homEquiv_apply_hom f)
  have hτ : τ = Pi.π (fun _ : Φ.fiber.obj T => M) t :=
    congrArg (fun z : Φ.fiber.obj T => Pi.π (fun _ : Φ.fiber.obj T => M) z)
      (Subsingleton.elim (default : Φ.fiber.obj T) t)
  have hδτ : δ ≫ τ = Φ.toPresheafFiber T t F.obj ≫ f :=
    (congrArg (fun z => δ ≫ z) hτ).trans
      ((congrArg (fun z => z ≫ Pi.π (fun _ : Φ.fiber.obj T => M) t) hδ).trans
        (Φ.skyscraperPresheafHomEquiv_app_π f T t))
  have hh : (unit ≫ δ) ≫ τ = 𝟙 M := h
  exact ((congrArg (fun z => unit ≫ z) hδτ).symm.trans
    (Category.assoc unit δ τ).symm).trans hh

/-- The constant-section unit gives an isomorphism from the coefficient
object to its actual point fiber. This retains the literal unit and germ. -/
theorem constantSheaf_unit_germ_isIso (M : A) (t : Φ.fiber.obj T) :
    IsIso ((constantSheafAdj J A hT).unit.app M ≫
      Φ.toPresheafFiber T t ((constantSheaf J A).obj M).obj) := by
  let e : Φ.sheafFiber.obj ((constantSheaf J A).obj M) ≅ M :=
    (Φ.constantSheafCompFiberIso A hT).app M
  have h : ((constantSheafAdj J A hT).unit.app M ≫
      Φ.toPresheafFiber T t ((constantSheaf J A).obj M).obj) ≫ e.hom =
      𝟙 M := by
    exact (Category.assoc _ _ _).trans
      (Φ.constantSheaf_unit_germ_comp_fiberIso A hT M t)
  have hunit : (constantSheafAdj J A hT).unit.app M ≫
      Φ.toPresheafFiber T t ((constantSheaf J A).obj M).obj = e.inv :=
    e.comp_hom_eq_id.mp h
  exact hunit.symm ▸ e.isIso_inv

end CategoryTheory.GrothendieckTopology.Point
