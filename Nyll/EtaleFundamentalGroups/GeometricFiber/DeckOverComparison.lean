/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.PointedCover

/-!
# Geometric deck pullback and the over-category

Pullback along an actual deck automorphism of a finite étale cover is
identified with inverse postcomposition in its over-category. The comparison
is the actual first projection of the scheme pullback.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} (A : FiniteEtale S) (σ : Aut A)

/-- The scheme isomorphism underlying an actual deck transformation. -/
def deckSchemeIso : A.left ≅ A.left where
  hom := σ.asIso.hom.left
  inv := σ.asIso.inv.left
  hom_inv_id := congrArg (fun f : A ⟶ A => f.left) σ.asIso.hom_inv_id
  inv_hom_id := congrArg (fun f : A ⟶ A => f.left) σ.asIso.inv_hom_id

/-- The underlying deck map followed by its inverse is the identity. -/
theorem deck_hom_inv :
    σ.asIso.hom.left ≫ σ.asIso.inv.left = 𝟙 A.left :=
  congrArg (fun f : A ⟶ A => f.left) σ.asIso.hom_inv_id

/-- The inverse underlying deck map followed by the deck map is the identity. -/
theorem deck_inv_hom :
    σ.asIso.inv.left ≫ σ.asIso.hom.left = 𝟙 A.left :=
  congrArg (fun f : A ⟶ A => f.left) σ.asIso.inv_hom_id

/-- The first projection identifies pullback by a deck map with its source. -/
def deckPullbackSourceIso (B : FiniteEtale A.left) :
    Limits.pullback B.hom σ.asIso.hom.left ≅ B.left where
  hom := Limits.pullback.fst B.hom σ.asIso.hom.left
  inv := Limits.pullback.lift (𝟙 B.left) (B.hom ≫ σ.asIso.inv.left) (by
    rw [Category.id_comp, Category.assoc, deck_inv_hom A σ]
    exact (Category.comp_id B.hom).symm)
  hom_inv_id := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, Limits.pullback.lift_snd, ← Category.assoc,
        Limits.pullback.condition, Category.assoc,
        deck_hom_inv A σ, Category.comp_id, Category.id_comp]
  inv_hom_id := Limits.pullback.lift_fst _ _ _

/-- The deck pullback identifies with inverse postcomposition over the cover. -/
def deckPullbackOverObjIso (B : FiniteEtale A.left) :
    (overEquiv A).functor.obj ((pullback σ.asIso.hom.left).obj B) ≅
      (Over.map σ.asIso.inv).obj ((overEquiv A).functor.obj B) := by
  let e : ((overEquiv A).functor.obj ((pullback σ.asIso.hom.left).obj B)).left ≅
      ((overEquiv A).functor.obj B).left :=
    MorphismProperty.Over.isoMk (deckPullbackSourceIso A σ B) (by
      change Limits.pullback.fst B.hom σ.asIso.hom.left ≫ (B.hom ≫ A.hom) =
        Limits.pullback.snd B.hom σ.asIso.hom.left ≫ A.hom
      rw [← Category.assoc, Limits.pullback.condition, Category.assoc,
        MorphismProperty.Over.w σ.asIso.hom])
  exact Over.isoMk e (by
    apply MorphismProperty.Over.Hom.ext
    change Limits.pullback.fst B.hom σ.asIso.hom.left ≫ (B.hom ≫ σ.asIso.inv.left) =
      Limits.pullback.snd B.hom σ.asIso.hom.left
    rw [← Category.assoc, Limits.pullback.condition, Category.assoc,
      deck_hom_inv A σ, Category.comp_id])

/-- Actual scheme pullback by a deck transformation is inverse
postcomposition under the finite-étale over-category equivalence. -/
def deckPullbackOverIso :
    pullback σ.asIso.hom.left ⋙ (overEquiv A).functor ≅
      (overEquiv A).functor ⋙ Over.map σ.asIso.inv :=
  NatIso.ofComponents (deckPullbackOverObjIso A σ) (fun f => by
    apply Over.OverMorphism.ext
    apply MorphismProperty.Over.Hom.ext
    change ((pullback σ.asIso.hom.left).map f).left ≫
        Limits.pullback.fst _ σ.asIso.hom.left =
      Limits.pullback.fst _ σ.asIso.hom.left ≫ f.left
    exact Limits.pullback.lift_fst _ _ _)

/-- The comparison uses the actual first projection, not a chosen
isomorphism between the covering schemes. -/
theorem deckPullbackOverIso_hom_left (B : FiniteEtale A.left) :
    ((deckPullbackOverIso A σ).hom.app B).left.left =
      Limits.pullback.fst B.hom σ.asIso.hom.left := rfl

end AlgebraicGeometry.FiniteEtale
