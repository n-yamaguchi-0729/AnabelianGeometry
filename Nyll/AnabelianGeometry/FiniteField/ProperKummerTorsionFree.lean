/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.KummerReductionTorsion
public import Nyll.AnabelianGeometry.FiniteField.ProperKummerReductionSurjective
public import Nyll.ProCGroups.Abelian.RestrictedTatePairingWeights

/-!
# Torsion-freeness of the actual proper prime-to-characteristic abelian quotient

The characteristic-primary part of a finite annihilator is cancelled using
the original invertible roots characters. Its remaining factor is eliminated
by the actual proper Kummer coefficient lifts. Consequently a uniform finite
annihilator suffices even if its order is divisible by the characteristic.
Neither a rational Tate comparison nor a torsion-free hypothesis is used.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open AlgebraicGeometry CategoryTheory
open AnabelianGeometry.WeightFiltration ProCGroups.Abelian

namespace AnabelianGeometry.FiniteField

private theorem exists_invertible_part_mul_characteristic_power
    (K : Type uGeom) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) (hN : 0 < N) :
    ∃ (m : ℕ+) (s : ℕ), IsUnit ((m : ℕ) : K) ∧ N = (m : ℕ) * p ^ s := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
      by_cases hd : p ∣ N
      · have hp := (Fact.out : p.Prime)
        have hpos : 0 < N / p := Nat.div_pos (Nat.le_of_dvd hN hd) hp.pos
        have hlt : N / p < N := Nat.div_lt_self hN hp.one_lt
        obtain ⟨m, s, hm, heq⟩ := ih (N / p) hlt hpos
        refine ⟨m, s + 1, hm, ?_⟩
        calc
          N = (N / p) * p := (Nat.div_mul_cancel hd).symm
          _ = (m : ℕ) * p ^ (s + 1) := by rw [heq, pow_succ, mul_assoc]
      · refine ⟨⟨N, hN⟩, 0, ?_, ?_⟩
        · exact isUnit_iff_ne_zero.mpr
            ((CharP.cast_eq_zero_iff K p N).not.mpr hd)
        · exact (mul_one N).symm

/-- Characteristic-primary torsion already vanishes in the actual
prime-to-characteristic quotient, by the original finite characters. -/
theorem primeToAbelianMk_eq_one_of_characteristic_power
    (K : Type uGeom) [Field K] [IsSepClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (g : G) (s : ℕ)
    (hg : primeToAbelianMk p G g ^ (p ^ s) = 1) :
    primeToAbelianMk p G g = 1 := by
  apply (primeToAbelianMk_eq_one_iff_unit_roots_characters p K g).mpr
  intro n hn top disc χ
  have hnot : ¬ p ∣ (n : ℕ) :=
    (CharP.cast_eq_zero_iff K p (n : ℕ)).not.mp hn.ne_zero
  have hcop : Nat.Coprime (p ^ s) (n : ℕ) :=
    ((Fact.out : p.Prime).coprime_pow_of_not_dvd hnot).symm
  have hp := congrArg (primeToAbelianRootsLift p K n hn χ) hg
  rw [map_pow, map_one] at hp
  apply ProCGroups.FiniteFixedCharacters.pow_cancel_of_coprime hcop
    (Subtype.ext ((mem_rootsOfUnity _ _).mp (χ g).property)) (one_pow (n : ℕ))
  exact hp.trans (one_pow (p ^ s)).symm

/-- Actual Kummer coefficient lifts eliminate every finite annihilator in
the canonical prime-to-characteristic abelian quotient. -/
theorem primeToAbelianMk_eq_one_of_pow_of_kummer_reductions
    (K : Type uGeom) [Field K] [IsSepClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    {X : Scheme.{uGeom}} [ConnectedSpace X]
    {Ω : Type uGeom} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (hlift : ∀ (m k : ℕ+), IsUnit ((m : ℕ) : K) → IsUnit ((k : ℕ) : K) →
      Function.Surjective (finiteKummerH1Reduce (K := K) X m k))
    (g : Aut (FiniteEtale.fiber ξ)) (N : ℕ) (hN : 0 < N)
    (hg : primeToAbelianMk p (Aut (FiniteEtale.fiber ξ)) g ^ N = 1) :
    primeToAbelianMk p (Aut (FiniteEtale.fiber ξ)) g = 1 := by
  obtain ⟨m, s, hm, hfactor⟩ :=
    exists_invertible_part_mul_characteristic_power K p N hN
  have hprimary :
      primeToAbelianMk p (Aut (FiniteEtale.fiber ξ)) (g ^ (m : ℕ)) ^ (p ^ s) = 1 := by
    rw [map_pow, ← pow_mul, ← hfactor]
    exact hg
  have hmzero : primeToAbelianMk p (Aut (FiniteEtale.fiber ξ)) g ^ (m : ℕ) = 1 := by
    rw [← map_pow]
    exact primeToAbelianMk_eq_one_of_characteristic_power K p (g ^ (m : ℕ)) s hprimary
  exact primeToAbelianMk_pow_eq_one_of_kummer_reduction K p ξ m hm
    (fun n hn => hlift n m hn hm) g hmzero

/-- For the literal smooth proper curve, every finite-order class in its
actual prime-to-characteristic geometric abelian quotient is trivial.
The function-field model and coefficient surjectivity are supplied inside. -/
theorem smoothProperPrimeToAbelianMk_eq_one_of_pow
    (K : Type uGeom) [Field K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    {C : Scheme.{uGeom}} [IsIntegral C] (c : C ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    {Ω : Type uGeom} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ C)
    (g : Aut (FiniteEtale.fiber ξ)) (N : ℕ) (hN : 0 < N)
    (hg : primeToAbelianMk p (Aut (FiniteEtale.fiber ξ)) g ^ N = 1) :
    primeToAbelianMk p (Aut (FiniteEtale.fiber ξ)) g = 1 := by
  apply primeToAbelianMk_eq_one_of_pow_of_kummer_reductions K p ξ ?_ g N hN hg
  intro m k hm hk
  apply smoothProperFiniteKummerH1Reduce_surjective c m k hm
  simpa only [PNat.mul_coe, Nat.cast_mul] using hm.mul hk

end AnabelianGeometry.FiniteField
