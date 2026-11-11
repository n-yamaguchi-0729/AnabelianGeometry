/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The one-place dimension-drop argument is adapted from the following Anthropic FLT source.
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RROpens_exists_finset_subset_ell_sub_sum_single_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

module

public import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.AdelicGenus
public import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.FiniteDimensionalLSpaceZero
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Simultaneous vanishing of finitely many Riemann–Roch spaces

For finitely many divisors with section dimensions at most `n`, choose exactly `n` distinct
places in any prescribed infinite set so that subtracting their sum kills every section space.
Each active space has a nonzero section, and away from its finite divisor and the divisor being
modified, subtraction of a place strictly lowers its dimension. A finite union of exceptional
sets works for the whole family.

No Riemann–Roch identity or algebraic closedness is required: finite dimensionality comes from
the existing curve-function-field producer. Over an algebraically closed base the selected
places have degree one, as needed in Tamagawa's Claims 4.12 and 4.14.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve Module

namespace AnabelianGeometry.FunctionField

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]

omit [IsCurveOver K F] in
private theorem lSpace_sub_single_le (D : Divisor K F) (P : Place K F) :
    LSpace (D - Finsupp.single P 1) ≤ LSpace D := by
  refine lSpace_mono ?_
  rw [Finsupp.le_def]
  intro Q
  rw [Finsupp.sub_apply]
  have hnonneg : (0 : ℤ) ≤ Finsupp.single P 1 Q := by
    rcases eq_or_ne Q P with rfl | hQP
    · rw [Finsupp.single_eq_same]
      exact zero_le_one
    · rw [Finsupp.single_eq_of_ne hQP]
  omega

private theorem exists_finset_ell_sub_single_le
    [FiniteDimensional K (LSpace (0 : Divisor K F))] (D : Divisor K F) :
    ∃ B : Finset (Place K F),
      ∀ P ∉ B, ell (D - Finsupp.single P 1) ≤ ell D - 1 := by
  classical
  have : FiniteDimensional K (LSpace D) := finiteDimensional_lSpace D
  by_cases hzero : ell D = 0
  · refine ⟨∅, fun P _ => ?_⟩
    have hle : ell (D - Finsupp.single P 1) ≤ ell D :=
      Submodule.finrank_mono (lSpace_sub_single_le D P)
    omega
  · have hbot : LSpace D ≠ ⊥ := by
      intro h
      apply hzero
      rw [ell, h, finrank_bot]
    obtain ⟨f, hfD, hf0⟩ := (Submodule.ne_bot_iff _).mp hbot
    obtain ⟨Δ, hΔord, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
    refine ⟨D.support ∪ Δ.support, fun P hP => ?_⟩
    rw [Finset.mem_union, not_or, Finsupp.notMem_support_iff,
      Finsupp.notMem_support_iff] at hP
    obtain ⟨hDP, hΔP⟩ := hP
    have hfP : P.ord f = 0 := by rw [← hΔord P, hΔP]
    have hfnot : f ∉ LSpace (D - Finsupp.single P 1) := by
      intro h
      have hbound := (mem_lSpace_iff_ord.mp h).resolve_left hf0 P
      rw [Finsupp.sub_apply, Finsupp.single_eq_same, hDP, hfP] at hbound
      omega
    have hlt : LSpace (D - Finsupp.single P 1) < LSpace D :=
      lt_of_le_of_ne (lSpace_sub_single_le D P) (fun h => hfnot (h ▸ hfD))
    have hdim : ell (D - Finsupp.single P 1) < ell D :=
      Submodule.finrank_lt_finrank_of_lt hlt
    omega

private theorem exists_finset_simultaneous_ell_eq_zero_aux
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {ι : Type*} [Finite ι] (n : ℕ) (D : ι → Divisor K F)
    (hD : ∀ i, ell (D i) ≤ n) (S : Set (Place K F)) (hS : S.Infinite) :
    ∃ T : Finset (Place K F), (↑T : Set (Place K F)) ⊆ S ∧ T.card = n ∧
      ∀ i, ell (D i - ∑ P ∈ T, Finsupp.single P 1) = 0 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  induction n generalizing D S with
  | zero =>
      refine ⟨∅, ?_, rfl, ?_⟩
      · rw [Finset.coe_empty]
        exact Set.empty_subset S
      · intro i
        simpa only [Finset.sum_empty, sub_zero] using Nat.eq_zero_of_le_zero (hD i)
  | succ n ih =>
      choose B hB using fun i => exists_finset_ell_sub_single_le (D i)
      let U : Finset (Place K F) := Finset.univ.biUnion B
      obtain ⟨P, hPS, hPU⟩ : ∃ P ∈ S, P ∉ U := by
        by_contra h
        push Not at h
        exact hS (U.finite_toSet.subset fun P hPS => h P hPS)
      have hnext : ∀ i, ell (D i - Finsupp.single P 1) ≤ n := by
        intro i
        have hPi : P ∉ B i := by
          intro hPi
          apply hPU
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hPi⟩
        have hdrop := hB i P hPi
        have hbound := hD i
        omega
      obtain ⟨T, hTS, hTcard, hTell⟩ :=
        ih (fun i => D i - Finsupp.single P 1) hnext
          (S \ {P}) (hS.sdiff (Set.finite_singleton P))
      have hPT : P ∉ T := fun h => (hTS h).2 rfl
      refine ⟨insert P T, ?_, ?_, ?_⟩
      · intro Q hQ
        rcases Finset.mem_insert.mp hQ with rfl | hQ
        · exact hPS
        · exact (hTS hQ).1
      · rw [Finset.card_insert_of_notMem hPT, hTcard]
      · intro i
        rw [Finset.sum_insert hPT, ← sub_sub]
        exact hTell i

/-- Simultaneously kill finitely many section spaces by exactly `n` distinct allowed places.
The finite-dimensionality needed for strict dimension drops is obtained from the existing
function-field theorem, rather than assumed as a Riemann–Roch identity. -/
theorem exists_finset_simultaneous_ell_eq_zero [Algebra.EssFiniteType K F]
    {ι : Type*} [Finite ι] (n : ℕ) (D : ι → Divisor K F)
    (hD : ∀ i, ell (D i) ≤ n) (S : Set (Place K F)) (hS : S.Infinite) :
    ∃ T : Finset (Place K F), (↑T : Set (Place K F)) ⊆ S ∧ T.card = n ∧
      ∀ i, ell (D i - ∑ P ∈ T, Finsupp.single P 1) = 0 := by
  obtain ⟨P, _⟩ := hS.nonempty
  have : Nonempty (Place K F) := ⟨P⟩
  have : FiniteDimensional K (LSpace (0 : Divisor K F)) :=
    finiteDimensional_lSpace_zero K F
  exact exists_finset_simultaneous_ell_eq_zero_aux n D hD S hS

/-- The simultaneous choice can also avoid any prescribed finite set. -/
theorem exists_finset_simultaneous_ell_eq_zero_avoiding [Algebra.EssFiniteType K F]
    {ι : Type*} [Finite ι] (n : ℕ) (D : ι → Divisor K F)
    (hD : ∀ i, ell (D i) ≤ n) (S : Set (Place K F)) (hS : S.Infinite)
    (B : Finset (Place K F)) :
    ∃ T : Finset (Place K F), (↑T : Set (Place K F)) ⊆ S ∧ T.card = n ∧
      Disjoint T B ∧ ∀ i, ell (D i - ∑ P ∈ T, Finsupp.single P 1) = 0 := by
  obtain ⟨T, hTS, hTcard, hTell⟩ :=
    exists_finset_simultaneous_ell_eq_zero n D hD
      (S \ (B : Set (Place K F))) (hS.sdiff B.finite_toSet)
  refine ⟨T, fun P hP => (hTS hP).1, hTcard, ?_, hTell⟩
  exact Finset.disjoint_left.mpr (fun P hPT hPB => (hTS hPT).2 hPB)

end AnabelianGeometry.FunctionField
