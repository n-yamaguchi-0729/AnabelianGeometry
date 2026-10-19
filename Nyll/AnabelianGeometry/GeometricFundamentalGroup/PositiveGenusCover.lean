/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.FiniteH1Cardinality
import Nyll.AlgebraicCurves.Models.Points.RationalPointExistence
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIntegralAlgClosed
import Nyll.EtaleFundamentalGroups.Cohomology.H1FiniteEtaleEffacement
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Nontrivial finite étale covers of positive-genus curves

A nonzero class in actual étale H¹ with coefficients in the p-th roots of
unity gives a nontrivial continuous character. Its open normal kernel is
realized by an actual pointed finite étale Galois cover of degree p.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- Positive genus supplies an actual finite étale Galois cover of every
prime degree, with a point over any chosen geometric point. No cover or
nontrivial fundamental-group quotient is assumed. -/
theorem exists_primeDegree_finiteEtale_cover_of_genus_pos
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F) (hg : 0 < genusFF K F)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ M.C) (p : ℕ) (hp : p.Prime) :
    ∃ (W : FiniteEtale M.C) (_ : IsGalois W)
      (ξW : Spec (.of Ω) ⟶ W.left),
      ξW ≫ W.hom = ξ ∧ Nat.card ((FiniteEtale.fiber ξ).obj W) = p := by
  have : GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  let A : AddCommGrpCat := AddCommGrpCat.of (Additive (rootsOfUnity p K))
  let H := Sheaf.H.{0}
    ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0}).obj A) 1
  have hcard : Nat.card H = p ^ (2 * genusFF K F) :=
    M.natCard_finiteH1_eq_pow_genus ε ⟨p, hp.pos⟩ ξ
  have : Finite H := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero _ hp.ne_zero)
  have : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hcard]
    exact Nat.one_lt_pow (by omega) hp.one_lt)
  obtain ⟨a, ha⟩ := exists_ne (0 : H)
  have hA : Nat.card A = p := HasEnoughRootsOfUnity.natCard_rootsOfUnity K p
  obtain ⟨W, hW, ξW, hξW, hdegree, _⟩ :=
    exists_primeDegree_galois_finiteEtale_cover_killing_h1 A ξ p hp hA a ha
  exact ⟨W, hW, ξW, hξW, hdegree⟩

end AnabelianGeometry
