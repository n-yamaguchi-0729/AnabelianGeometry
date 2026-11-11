/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.PrimeToAbelianRoots
public import Nyll.AnabelianGeometry.WeightFiltration.BoundaryCoefficientReduction
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Surjectivity

/-!
# Invertible torsion detected by actual Kummer coefficient lifts

Surjectivity of the genuine finite-coefficient H¹ reduction eliminates
torsion of that exponent in the canonical prime-to-characteristic quotient.
This intermediate comparison is later supplied by the curve residue sequence.
It uses no characteristic-zero assumption or rational Tate module.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open AlgebraicGeometry CategoryTheory
open EtaleFundamentalGroups.Cohomology EtaleFundamentalGroups.Inertia
open AnabelianGeometry.WeightFiltration ProCGroups.Abelian

namespace AnabelianGeometry.FiniteField

/-- Actual Kummer coefficient lifts kill invertible-exponent torsion in the
canonical prime-to-p abelian quotient, including its finite torsion. -/
theorem primeToAbelianMk_pow_eq_one_of_kummer_reduction
    (K : Type uGeom) [Field K] [IsSepClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    {X : Scheme.{uGeom}} [ConnectedSpace X]
    {Ω : Type uGeom} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (k : ℕ+) (hk : IsUnit ((k : ℕ) : K))
    (hlift : ∀ (m : ℕ+), IsUnit ((m : ℕ) : K) →
      Function.Surjective (finiteKummerH1Reduce (K := K) X m k))
    (g : Aut (FiniteEtale.fiber ξ))
    (hg : primeToAbelianMk p (Aut (FiniteEtale.fiber ξ)) g ^ (k : ℕ) = 1) :
    primeToAbelianMk p (Aut (FiniteEtale.fiber ξ)) g = 1 := by
  apply (primeToAbelianMk_eq_one_iff_unit_roots_characters p K g).mpr
  intro m hm top disc χ
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (m : ℕ) K))
  let B := AddCommGrpCat.of (Additive (rootsOfUnity ((m * k : ℕ+) : ℕ) K))
  let : TopologicalSpace (rootsOfUnity ((m * k : ℕ+) : ℕ) K) := ⊥
  let : DiscreteTopology (rootsOfUnity ((m * k : ℕ+) : ℕ) K) := ⟨rfl⟩
  obtain ⟨a, ha⟩ := h1Character_surjective A ξ χ
  obtain ⟨b, hb⟩ := hlift m hm a
  let ψ := h1Character B ξ b
  have hmk : IsUnit (((m * k : ℕ+) : ℕ) : K) := by
    simpa only [PNat.mul_coe, Nat.cast_mul] using hm.mul hk
  let ψ' := primeToAbelianRootsLift p K (m * k) hmk ψ
  have hp : ψ g ^ (k : ℕ) = 1 := by
    have h := congrArg ψ' hg
    rw [map_pow, map_one] at h
    exact h
  have hn := congrArg (fun f => f g)
    (h1Character_naturality (kummerCoefficientReduction K m k) ξ b)
  change rootsOfUnityPowerTransition K (dvd_mul_right (m : ℕ) (k : ℕ))
      (ψ g) = h1Character A ξ (finiteKummerH1Reduce X m k b) g at hn
  rw [hb, ha] at hn
  apply Subtype.ext
  have hval := congrArg Subtype.val hn
  change ((show rootsOfUnity ((m * k : ℕ+) : ℕ) K from ψ g) : Kˣ) ^
    (((m * k : ℕ+) : ℕ) / (m : ℕ)) = (χ g : Kˣ) at hval
  have hdiv : (((m * k : ℕ+) : ℕ) / (m : ℕ)) = (k : ℕ) :=
    Nat.mul_div_cancel_left (k : ℕ) m.pos
  rw [hdiv] at hval
  have hp' : (show rootsOfUnity ((m * k : ℕ+) : ℕ) K from ψ g) ^ (k : ℕ) = 1 := hp
  exact hval.symm.trans (congrArg (fun z : rootsOfUnity ((m * k : ℕ+) : ℕ) K => z.val) hp')

end AnabelianGeometry.FiniteField
