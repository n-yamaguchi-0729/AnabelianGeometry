/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivOfPoint
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The original point ideal on a product

The constant graph is the actual inverse image of the original section
under the first projection. Its Cartesian universal property identifies
their full kernel ideal sheaves, including their scheme structures.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  (p : S ⟶ X) (hp : p ≫ f = 𝟙 S)

/-- The original constant graph is the actual base change of the
original section along the first product projection. -/
theorem constantGraph_isPullback :
    IsPullback (graphOver f (g ≫ p) (by rw [Category.assoc, hp, Category.comp_id])) g
      (pullback.fst f g) p := by
  refine IsPullback.mk' (graphOver_fst f (g ≫ p) _) ?_ ?_
  · intro T a b h₁ h₂
    have h := congrArg (fun k : T ⟶ pullback f g => k ≫ pullback.snd f g) h₁
    simpa only [Category.assoc, graphOver_snd, Category.comp_id] using h
  · intro T a b h
    have hab : a ≫ pullback.snd f g ≫ g = b := by
      rw [← pullback.condition, ← Category.assoc, h, Category.assoc, hp,
        Category.comp_id]
    refine ⟨a ≫ pullback.snd f g, ?_, (Category.assoc _ _ _).trans hab⟩
    apply pullback.hom_ext
    · calc
        ((a ≫ pullback.snd f g) ≫ graphOver f (g ≫ p) _) ≫ pullback.fst f g =
            (a ≫ pullback.snd f g ≫ g) ≫ p := by
          simp only [Category.assoc, graphOver_fst]
        _ = a ≫ pullback.fst f g := by
          rw [hab]
          exact h.symm
    · rw [Category.assoc, graphOver_snd, Category.comp_id]

/-- The constant graph kernel equals the original point kernel pulled
back along the first projection, as an equality of actual ideals. -/
theorem pointKernel_comap_fst [IsSeparated f] :
    p.ker.comap (pullback.fst f g) =
      (graphOver f (g ≫ p) (by rw [Category.assoc, hp, Category.comp_id])).ker := by
  have : IsClosedImmersion (p ≫ f) := by
    rw [hp]
    infer_instance
  have : IsClosedImmersion p := .of_comp p f
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← (constantGraph_isPullback f g p hp).isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

end AlgebraicGeometry
