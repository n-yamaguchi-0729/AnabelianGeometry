/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Sites.Sieves.Basic
public import Mathlib.CategoryTheory.Sites.Sieves.Presieve

/-!
# A genuine common cover for two original Cech representatives

The actual fiber product of two singleton covers is again a singleton
cover. Every arrow in the intersection of the two original covering
sieves factors through this same fiber product by its universal
property. Thus two actual extension lifts can be restricted to a
common covering object without a new covering assumption.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory Limits

namespace EtaleCohomology

/-- The actual categorical pullback is a common singleton cover of
the original object whenever both original arrows are covers. -/
theorem cechCommonCover_covering
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {T V W : C} (f : V ⟶ T) (g : W ⟶ T) [HasPullback f g]
    (hf : Sieve.generate (Presieve.singleton f) ∈ J T)
    (hg : Sieve.generate (Presieve.singleton g) ∈ J T) :
    Sieve.generate (Presieve.singleton (pullback.fst f g ≫ f)) ∈ J T := by
  have hle : Sieve.generate (Presieve.singleton f) ⊓
      Sieve.generate (Presieve.singleton g) ≤
        Sieve.generate (Presieve.singleton (pullback.fst f g ≫ f)) := by
    intro Z h hh
    obtain ⟨_, a, _, ⟨⟩, ha⟩ := hh.1
    obtain ⟨_, b, _, ⟨⟩, hb⟩ := hh.2
    refine ⟨pullback f g, pullback.lift a b (ha.trans hb.symm),
      pullback.fst f g ≫ f, Presieve.singleton_self _, ?_⟩
    rw [← Category.assoc, pullback.lift_fst]
    exact ha
  exact J.superset_covering hle (J.intersection_covering hf hg)

end EtaleCohomology
