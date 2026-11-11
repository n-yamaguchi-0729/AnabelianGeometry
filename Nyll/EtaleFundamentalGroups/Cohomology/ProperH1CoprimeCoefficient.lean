/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.GaloisH1Descent
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Algebra.CharP.Basic

/-! # Finite coefficients coprime to the actual covering index -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry

namespace EtaleFundamentalGroups.Cohomology

/-- The actual covering stabilizer has positive finite index, proved from
its finite geometric orbit. -/
theorem pointedCoverOpenSubgroup_index_pos
    {S : Scheme} [ConnectedSpace S] (A : FiniteEtale S)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ A.left) :
    0 < (pointedCoverOpenSubgroup A geom).toSubgroup.index := by
  let G := Aut (FiniteEtale.fiber (geom ≫ A.hom))
  let H : OpenSubgroup G := pointedCoverOpenSubgroup A geom
  have : Finite (G ⧸ H.toSubgroup) :=
    Finite.of_equiv (MulAction.orbit G (FiniteEtale.liftedFiberPoint A geom))
      (MulAction.orbitEquivQuotientStabilizer G (FiniteEtale.liftedFiberPoint A geom))
  change 0 < Nat.card (G ⧸ H.toSubgroup)
  exact Nat.card_pos

/-- Roots-of-unity coefficients can be chosen nontrivial, invertible in the
base field, and coprime to the actual covering index in every characteristic. -/
theorem exists_invertible_rootsOfUnity_coefficient_coprime_index
    (K : Type) [Field K] [IsAlgClosed K]
    {S : Scheme} [ConnectedSpace S] (A : FiniteEtale S)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ A.left) :
    ∃ n : ℕ+, 1 < (n : ℕ) ∧ IsUnit ((n : ℕ) : K) ∧
      (Nat.card (Multiplicative
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))))).Coprime
          (pointedCoverOpenSubgroup A geom).toSubgroup.index := by
  let d := (pointedCoverOpenSubgroup A geom).toSubgroup.index
  have hd : 0 < d := pointedCoverOpenSubgroup_index_pos A geom
  obtain ⟨l, hbound, hl⟩ := Nat.exists_infinite_primes (max d (ringChar K) + 1)
  have hdl : d < l := lt_of_le_of_lt (le_max_left _ _)
    (lt_of_lt_of_le (Nat.lt_succ_self _) hbound)
  have hchar : ringChar K < l := lt_of_le_of_lt (le_max_right _ _)
    (lt_of_lt_of_le (Nat.lt_succ_self _) hbound)
  have hlK : (l : K) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime K hl (ne_of_lt hchar)
  let n : ℕ+ := ⟨l, hl.pos⟩
  have : NeZero l := ⟨hl.ne_zero⟩
  have : NeZero (l : K) := ⟨hlK⟩
  refine ⟨n, hl.one_lt, isUnit_iff_ne_zero.mpr hlK, ?_⟩
  change (Nat.card (rootsOfUnity l K)).Coprime d
  rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity]
  exact hl.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hd hdl)

/-- Nontrivial roots-of-unity coefficients can always be chosen coprime
to the actual covering index. -/
theorem exists_rootsOfUnity_coefficient_coprime_index
    (K : Type) [Field K] [IsAlgClosed K]
    {S : Scheme} [ConnectedSpace S] (A : FiniteEtale S)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ A.left) :
    ∃ n : ℕ+, 1 < (n : ℕ) ∧
      (Nat.card (Multiplicative
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))))).Coprime
          (pointedCoverOpenSubgroup A geom).toSubgroup.index := by
  obtain ⟨n, hn, _, hcop⟩ :=
    exists_invertible_rootsOfUnity_coefficient_coprime_index K A geom
  exact ⟨n, hn, hcop⟩

end EtaleFundamentalGroups.Cohomology
