/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivOfPoint
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalAdicCup
public import Nyll.EtaleCohomology.Classical.RationalExternalCupPullback
public import Nyll.EtaleCohomology.Classical.RationalKunnethMap
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Actual graph pullback of rational external cup

The original `graphOver` used for the graph–diagonal intersection has first
projection the given map and second projection the identity. Its pullback
of the original external cup therefore applies cohomological pullback to
the first factor and then uses cup. The identity graph is the original
diagonal, and the formulas also identify the actual Künneth maps.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open scoped DirectSum TensorProduct

namespace AlgebraicGeometry

/-- The original graph of the identity is the actual scheme diagonal. -/
theorem graphOver_id_eq_diagonal {X S : Scheme.{u}} (f : X ⟶ S) :
    graphOver f (𝟙 X) (Category.id_comp f) = pullback.diagonal f := by
  apply pullback.hom_ext
  · exact (graphOver_fst f (𝟙 X) (Category.id_comp f)).trans
      (pullback.diagonal_fst f).symm
  · exact (graphOver_snd f (𝟙 X) (Category.id_comp f)).trans
      (pullback.diagonal_snd f).symm

end AlgebraicGeometry

namespace EtaleCohomology.Classical

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y S : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (v : Y ⟶ X) (hv : v ≫ f = g)

/-- Pullback along the original graph is cup after pullback of the first
factor by the original scheme map. -/
theorem rationalEllAdicExternalCup_graphOver (a b c : ℕ) (h : a + b = c)
    (x : rationalEllAdicCohomology ℓ X a) (y : rationalEllAdicCohomology ℓ Y b) :
    rationalEllAdicCohomologyPullback ℓ (graphOver f v hv) c
        (rationalEllAdicExternalCup ℓ f g a b c h x y) =
      rationalEllAdicCup Y ℓ a b c h (rationalEllAdicCohomologyPullback ℓ v a x) y := by
  simpa only [graphOver_fst, graphOver_snd,
    rationalEllAdicCohomologyPullback_id, Module.End.one_apply] using
    rationalEllAdicExternalCup_pullback ℓ f g (graphOver f v hv) a b c h x y

/-- The actual Künneth component followed by the original graph pullback
is the tensor map of cup with the first factor pulled back by that map. -/
theorem rationalEllAdicKunnethComponent_graphOver (a b c : ℕ) (h : a + b = c) :
    (rationalEllAdicCohomologyPullback ℓ (graphOver f v hv) c).comp
        (rationalEllAdicKunnethComponent ℓ f g a b c h) =
      TensorProduct.lift ((rationalEllAdicCup Y ℓ a b c h).compl₁₂
        (rationalEllAdicCohomologyPullback ℓ v a)
        (LinearMap.id : rationalEllAdicCohomology ℓ Y b →ₗ[ℚ_[ℓ]]
          rationalEllAdicCohomology ℓ Y b)) := by
  apply TensorProduct.ext'
  intro x y
  exact rationalEllAdicExternalCup_graphOver ℓ f g v hv a b c h x y

/-- Pullback by the original graph on the full actual Künneth map is
the direct sum of cups with the original first-factor pullback. -/
theorem rationalEllAdicKunnethMap_graphOver (n : ℕ) :
    (rationalEllAdicCohomologyPullback ℓ (graphOver f v hv) n).comp
        (rationalEllAdicKunnethMap ℓ f g n) =
      DirectSum.toModule ℚ_[ℓ] (Fin (n + 1)) (rationalEllAdicCohomology ℓ Y n)
        (fun d => TensorProduct.lift
          ((rationalEllAdicCup Y ℓ d.val (n - d.val) n
            (Nat.add_sub_of_le (Nat.le_of_lt_succ d.isLt))).compl₁₂
            (rationalEllAdicCohomologyPullback ℓ v d.val)
            (LinearMap.id : rationalEllAdicCohomology ℓ Y (n - d.val) →ₗ[ℚ_[ℓ]]
              rationalEllAdicCohomology ℓ Y (n - d.val)))) := by
  apply DirectSum.linearMap_ext
  intro d
  apply TensorProduct.ext'
  intro x y
  simpa only [LinearMap.comp_apply, rationalEllAdicKunnethMap_lof_tmul,
    DirectSum.toModule_lof, TensorProduct.lift.tmul,
    LinearMap.compl₁₂_apply, LinearMap.id_apply] using
    rationalEllAdicExternalCup_graphOver ℓ f g v hv d.val (n - d.val) n
      (Nat.add_sub_of_le (Nat.le_of_lt_succ d.isLt)) x y

end EtaleCohomology.Classical
