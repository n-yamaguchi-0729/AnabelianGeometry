/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.OpenDivisorCohomologyInjection

/-! # Powers of the named actual open Kummer cover

The existing additive divisor-to-derived-cohomology map owns this law. No
identification of an arbitrary character with a named cover is assumed here.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory

namespace AlgebraicCurve.CurveModel.OpenKummer

variable {K : Type u} [Field K] [IsSepClosed K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
  {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hinterior : ∀ (y : X) (x : closedPoints M.C),
    x.val = j y → M.placeOfPoint x ∉ S)
  (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)

/-- The named actual class of the power function is the corresponding multiple. -/
theorem kummerEtaleClass_pow
    (w : Pic0.openKummerUnits K F S n) (q : ℕ) :
    kummerEtaleClass M S n (w ^ q) j hj hinterior hn xi =
      q • kummerEtaleClass M S n w j hj hinterior hn xi := by
  let f : Additive (Pic0.openKummerUnits K F S n) →+
      Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1 :=
    (quotientCohomology M S n j hj hinterior hn xi).comp
      (QuotientGroup.mk' (Pic0.openKummerPowers K F S n)).toAdditive
  exact map_nsmul f q (Additive.ofMul w)

end AlgebraicCurve.CurveModel.OpenKummer
