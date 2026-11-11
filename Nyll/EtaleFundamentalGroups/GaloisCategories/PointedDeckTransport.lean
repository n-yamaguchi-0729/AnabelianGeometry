/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCategories.PointedOverTransport

/-!
# Deck transformations and conjugation on pointed cover fibers

An automorphism of the covering object acts by inverse postcomposition on
its over-category. Choosing an ambient monodromy element with the same
effect on the distinguished point compares its induced fundamental-group
map with conjugation. The comparison uses the actual over-category functor.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v} C]
variable (F : C ⥤ FintypeCat.{w}) [PreGaloisCategory C] [FiberFunctor F]
variable {X : C} (x : F.obj X) (σ : Aut X) (g : Aut F)
variable (h : F.map σ.asIso.hom x = g • x)

omit [PreGaloisCategory C] [FiberFunctor F] in
include h in
/-- The deck-transformed fiber has the point prescribed by the ambient monodromy. -/
theorem deckFiberPoint (U : Over X)
    (z : (fiberOver F x).obj ((Over.map σ.asIso.inv).obj U)) :
    F.map U.hom z.1 = g • x := by
  have hz : F.map σ.asIso.inv (F.map U.hom z.1) = x := by
    have hz := z.2
    change F.map (U.hom ≫ σ.asIso.inv) z.1 = x at hz
    rw [F.map_comp, FintypeCat.comp_apply] at hz
    exact hz
  calc
    F.map U.hom z.1 =
        F.map σ.asIso.hom (F.map σ.asIso.inv (F.map U.hom z.1)) :=
      (FintypeCat.inv_hom_id_apply (F.mapIso σ.asIso) _).symm
    _ = F.map σ.asIso.hom x := congrArg (F.map σ.asIso.hom) hz
    _ = g • x := h

/-- Compare the deck-transformed pointed fiber using the chosen ambient monodromy. -/
def pointedDeckFiberEquiv (U : Over X) :
    (fiberOver F x).obj ((Over.map σ.asIso.inv).obj U) ≃ (fiberOver F x).obj U where
  toFun z := ⟨g⁻¹ • z.1, by
    exact ((mulAction_naturality F g⁻¹ U.hom z.1).symm).trans
      ((congrArg (g⁻¹ • ·) (deckFiberPoint F x σ g h U z)).trans
        (inv_smul_smul g x))⟩
  invFun z := ⟨g • z.1, by
    change F.map (U.hom ≫ σ.asIso.inv) (g • z.1) = x
    rw [F.map_comp, FintypeCat.comp_apply,
      ← mulAction_naturality F g U.hom z.1, z.2, ← h]
    exact FintypeCat.hom_inv_id_apply (F.mapIso σ.asIso) x⟩
  left_inv z := by
    apply Subtype.ext
    exact smul_inv_smul g z.1
  right_inv z := by
    apply Subtype.ext
    exact inv_smul_smul g z.1

/-- The geometric deck functor on the over-category, pointed using ambient
monodromy with the same endpoint as the deck transformation. -/
def pointedDeckFiberIso :
    Over.map σ.asIso.inv ⋙ fiberOver F x ≅ fiberOver F x :=
  NatIso.ofComponents
    (fun U => FintypeCat.equivEquivIso (pointedDeckFiberEquiv F x σ g h U))
    (fun f => by
      apply FintypeCat.hom_ext
      intro z
      apply Subtype.ext
      exact mulAction_naturality F g⁻¹ f.left z.1)

/-- The ambient image of the actual deck-induced map on pointed fiber
automorphisms is conjugation by the chosen ambient monodromy element. -/
theorem extendFiberOverAut_pointedDeck
    (a : Aut (fiberOver F x)) :
    extendFiberOverAut F x
        (autHomOfCompIso (Over.map σ.asIso.inv) (pointedDeckFiberIso F x σ g h) a) =
      g⁻¹ * extendFiberOverAut F x a * g := by
  let b := autFiberOverMulEquivStabilizer F x a
  have hb : restrictAutToFiberOver F x b = a :=
    (autFiberOverMulEquivStabilizer F x).symm_apply_apply a
  have hfix : (g⁻¹ * b.1 * g) • x = x := by
    rw [mul_smul, mul_smul, ← h]
    rw [mulAction_naturality F b.1 σ.asIso.hom x, b.2, h, inv_smul_smul]
  let c : MulAction.stabilizer (Aut F) x := ⟨g⁻¹ * b.1 * g, hfix⟩
  have hc :
      autHomOfCompIso (Over.map σ.asIso.inv) (pointedDeckFiberIso F x σ g h)
        (restrictAutToFiberOver F x b) = restrictAutToFiberOver F x c := by
    apply Aut.ext
    apply Iso.ext
    ext U z
    apply Subtype.ext
    change g⁻¹ • (b.1 • (g • z.1)) = (g⁻¹ * b.1 * g) • z.1
    rw [mul_smul, mul_smul]
  rw [hb] at hc
  have he : extendFiberOverAut F x (restrictAutToFiberOver F x c) = c.1 :=
    congrArg Subtype.val ((autFiberOverMulEquivStabilizer F x).apply_symm_apply c)
  exact (congrArg (extendFiberOverAut F x) hc).trans he

end CategoryTheory.PreGaloisCategory
