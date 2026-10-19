/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.OpenCurveResidueRanks
import Nyll.JacobianVarieties.Kummer.OpenFiniteH1Cardinality

/-!
# Finiteness of actual curve cohomology

The finite-coefficient cohomology groups are finite for both empty and
nonempty boundary. This supplies compactness for discrete coefficient systems.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve NeronModelInfra

namespace AnabelianGeometry.WeightFiltration

/-- Actual finite-coefficient H¹ of an open curve is finite, also for empty boundary. -/
theorem finite_finiteKummerH1
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F) (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    [Finite (M.openBoundaryPlaces j)] (n : ℕ+)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    Finite (FiniteKummerH1 K X n) := by
  classical
  let : Fintype (M.openBoundaryPlaces j) := Fintype.ofFinite _
  by_cases h : Nonempty (M.openBoundaryPlaces j)
  · apply Nat.finite_of_card_ne_zero
    rw [M.natCard_open_finiteH1_eq_pow_genus_boundary ε j hj (Classical.choice h) n xi]
    exact pow_ne_zero _ n.ne_zero
  · have : IsEmpty (M.openBoundaryPlaces j) := ⟨fun v => h ⟨v⟩⟩
    have hn : IsUnit ((n : ℕ) : K) :=
      isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
    have : Finite (finiteResidue M n j hj hn xi).ker := by
      apply Nat.finite_of_card_ne_zero
      rw [natCard_finiteResidue_ker M ε n j hj hn xi]
      exact pow_ne_zero _ n.ne_zero
    apply Finite.of_surjective
      (fun c : (finiteResidue M n j hj hn xi).ker => c.val)
    intro c
    refine ⟨⟨c, ?_⟩, rfl⟩
    change finiteResidue M n j hj hn xi c = 0
    funext v
    exact isEmptyElim v

end AnabelianGeometry.WeightFiltration
