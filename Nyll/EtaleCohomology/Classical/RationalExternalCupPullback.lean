/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AdicCupPullback
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ExternalCupPullbackComposition
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalAdicCup
public import Nyll.EtaleCohomology.Classical.RationalKunnethMap
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Pullback and the diagonal for the actual rational external cup

Pullback of the external product is the cup of pullback by the two actual
composite projections. In particular the original diagonal recovers cup
on the original rational adic cohomology. The same identity holds for the
actual Künneth component and full direct-sum map.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open scoped DirectSum TensorProduct

namespace EtaleCohomology.Classical

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- Pulling back the actual external cup computes the cup of the two
original composite-projection pullbacks. -/
theorem rationalEllAdicExternalCup_pullback {T : Scheme.{u}}
    (j : T ⟶ pullback f g) (a b c : ℕ) (h : a + b = c)
    (x : rationalEllAdicCohomology ℓ X a) (y : rationalEllAdicCohomology ℓ Y b) :
    rationalEllAdicCohomologyPullback ℓ j c
        (rationalEllAdicExternalCup ℓ f g a b c h x y) =
      rationalEllAdicCup T ℓ a b c h
        (rationalEllAdicCohomologyPullback ℓ (j ≫ pullback.fst f g) a x)
        (rationalEllAdicCohomologyPullback ℓ (j ≫ pullback.snd f g) b y) := by
  rw [rationalEllAdicExternalCup_apply, rationalEllAdicCohomologyPullback_cup]
  exact congrArg₂ (fun v w => rationalEllAdicCup T ℓ a b c h v w)
    (LinearMap.congr_fun
      (rationalEllAdicCohomologyPullback_comp j (pullback.fst f g) ℓ a) x).symm
    (LinearMap.congr_fun
      (rationalEllAdicCohomologyPullback_comp j (pullback.snd f g) ℓ b) y).symm

/-- The map into the actual fibre product induced by a pair of scheme
morphisms pulls external cup back to the cup of those original maps. -/
theorem rationalEllAdicExternalCup_lift {T : Scheme.{u}}
    (v : T ⟶ X) (w : T ⟶ Y) (hw : v ≫ f = w ≫ g)
    (a b c : ℕ) (h : a + b = c)
    (x : rationalEllAdicCohomology ℓ X a) (y : rationalEllAdicCohomology ℓ Y b) :
    rationalEllAdicCohomologyPullback ℓ (pullback.lift v w hw) c
        (rationalEllAdicExternalCup ℓ f g a b c h x y) =
      rationalEllAdicCup T ℓ a b c h
        (rationalEllAdicCohomologyPullback ℓ v a x)
        (rationalEllAdicCohomologyPullback ℓ w b y) := by
  simpa only [pullback.lift_fst, pullback.lift_snd] using
    rationalEllAdicExternalCup_pullback ℓ f g (pullback.lift v w hw) a b c h x y

/-- On the original tensor factors, pullback of the actual Künneth
component is the bilinear cup of the original composite pullbacks. -/
theorem rationalEllAdicKunnethComponent_pullback {T : Scheme.{u}}
    (j : T ⟶ pullback f g) (a b c : ℕ) (h : a + b = c) :
    (rationalEllAdicCohomologyPullback ℓ j c).comp
        (rationalEllAdicKunnethComponent ℓ f g a b c h) =
      TensorProduct.lift ((rationalEllAdicCup T ℓ a b c h).compl₁₂
        (rationalEllAdicCohomologyPullback ℓ (j ≫ pullback.fst f g) a)
        (rationalEllAdicCohomologyPullback ℓ (j ≫ pullback.snd f g) b)) := by
  apply TensorProduct.ext'
  intro x y
  exact rationalEllAdicExternalCup_pullback ℓ f g j a b c h x y

/-- The original scheme diagonal pulls the external cup back to cup
on the original rational adic cohomology. -/
theorem rationalEllAdicExternalCup_diagonal (a b c : ℕ) (h : a + b = c)
    (x : rationalEllAdicCohomology ℓ X a) (y : rationalEllAdicCohomology ℓ X b) :
    rationalEllAdicCohomologyPullback ℓ (pullback.diagonal f) c
        (rationalEllAdicExternalCup ℓ f f a b c h x y) =
      rationalEllAdicCup X ℓ a b c h x y := by
  simpa only [pullback.diagonal_fst, pullback.diagonal_snd,
    rationalEllAdicCohomologyPullback_id, Module.End.one_apply] using
    rationalEllAdicExternalCup_pullback ℓ f f (pullback.diagonal f) a b c h x y

/-- Pullback along the actual diagonal identifies the original Künneth
component followed by pullback with the linear map of cup. -/
theorem rationalEllAdicKunnethComponent_diagonal (a b c : ℕ) (h : a + b = c) :
    (rationalEllAdicCohomologyPullback ℓ (pullback.diagonal f) c).comp
        (rationalEllAdicKunnethComponent ℓ f f a b c h) =
      TensorProduct.lift (rationalEllAdicCup X ℓ a b c h) := by
  apply TensorProduct.ext'
  intro x y
  exact rationalEllAdicExternalCup_diagonal ℓ f a b c h x y

/-- Diagonal pullback of the full actual Künneth map is the direct sum
of the original cups in complementary degrees. -/
theorem rationalEllAdicKunnethMap_diagonal (n : ℕ) :
    (rationalEllAdicCohomologyPullback ℓ (pullback.diagonal f) n).comp
        (rationalEllAdicKunnethMap ℓ f f n) =
      DirectSum.toModule ℚ_[ℓ] (Fin (n + 1)) (rationalEllAdicCohomology ℓ X n)
        (fun d => TensorProduct.lift
          (rationalEllAdicCup X ℓ d.val (n - d.val) n
            (Nat.add_sub_of_le (Nat.le_of_lt_succ d.isLt)))) := by
  apply DirectSum.linearMap_ext
  intro d
  apply TensorProduct.ext'
  intro x y
  simpa only [LinearMap.comp_apply, rationalEllAdicKunnethMap_lof_tmul,
    DirectSum.toModule_lof, TensorProduct.lift.tmul] using
    rationalEllAdicExternalCup_diagonal ℓ f d.val (n - d.val) n
      (Nat.add_sub_of_le (Nat.le_of_lt_succ d.isLt)) x y

end EtaleCohomology.Classical
