/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.ProperKummerReductionSurjective
public import Nyll.AnabelianGeometry.FiniteField.KummerReductionTorsion
public import Nyll.AnabelianGeometry.WeightFiltration.FiniteResidueSequence

/-!
# Actual open-curve coefficient lifts and prime-to-characteristic torsion

The proper Picard lift and the sum-zero boundary lift give surjectivity of
the genuine open-curve Kummer coefficient reduction. Character detection
then rules out every invertible finite exponent in the actual prime-to-p
geometric abelian quotient. Wild inertia is never replaced by a tame model.
-/

@[expose] public section

universe u v

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve NeronModelInfra
open EtaleFundamentalGroups.Cohomology
open AnabelianGeometry.WeightFiltration ProCGroups.Abelian

namespace AnabelianGeometry.FiniteField

/-- The original Kummer coefficient reduction on an open smooth curve is
surjective at invertible exponents, including an empty boundary. -/
theorem openFiniteKummerH1Reduce_surjective
    {K : Type u} {F : Type v} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (M : CurveModel K F) (m k : ℕ+)
    {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hm : IsUnit ((m : ℕ) : K)) (hmk : IsUnit (((m * k : ℕ+) : ℕ) : K))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    [Finite (M.openBoundaryPlaces j)] :
    Function.Surjective (finiteKummerH1Reduce (K := K) X m k) := by
  classical
  let : Fintype (M.openBoundaryPlaces j) := Fintype.ofFinite _
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  intro a
  obtain ⟨v, hv⟩ := boundaryResidueReduce_surjective (m := m) (n := m * k)
    (dvd_mul_right (m : ℕ) (k : ℕ)) (finiteBoundaryResidue M m j hj hm ξ a)
  obtain ⟨b, hb⟩ := finiteBoundaryResidue_surjective_all M (m * k) j hj hmk ξ ε v
  have hz : a - finiteKummerH1Reduce X m k b ∈
      (finiteBoundaryResidue M m j hj hm ξ).ker := by
    change finiteBoundaryResidue M m j hj hm ξ (a - finiteKummerH1Reduce X m k b) = 0
    rw [map_sub, finiteBoundaryResidue_coefficientReduction M m k j hj hm hmk ξ b,
      hb, hv, sub_self]
  rw [← (compactification_finiteResidue_exact M m j hj hm ξ ε).2.2] at hz
  obtain ⟨d, hd⟩ := hz
  obtain ⟨e, he⟩ := properFiniteKummerH1Reduce_surjective M m k hm hmk d
  refine ⟨b + constantCohomologyPullback j
    (AddCommGrpCat.of (Additive (rootsOfUnity ((m * k : ℕ+) : ℕ) K))) 1 e, ?_⟩
  rw [map_add, finiteKummerH1Reduce_pullback, he, hd]
  abel

/-- The literal prime-to-p abelian quotient of the original open curve
has no nontrivial element annihilated by an invertible exponent. -/
theorem openPrimeToAbelianMk_pow_eq_one
    {K : Type u} {F : Type v} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (M : CurveModel K F)
    {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    [Finite (M.openBoundaryPlaces j)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (k : ℕ+) (hk : IsUnit ((k : ℕ) : K))
    (g : Aut (FiniteEtale.fiber ξ))
    (hg : primeToAbelianMk p (Aut (FiniteEtale.fiber ξ)) g ^ (k : ℕ) = 1) :
    primeToAbelianMk p (Aut (FiniteEtale.fiber ξ)) g = 1 := by
  apply primeToAbelianMk_pow_eq_one_of_kummer_reduction K p ξ k hk _ g hg
  intro m hm
  have hmk : IsUnit (((m * k : ℕ+) : ℕ) : K) := by
    simpa only [PNat.mul_coe, Nat.cast_mul] using hm.mul hk
  exact openFiniteKummerH1Reduce_surjective M m k j hj hm hmk ξ

end AnabelianGeometry.FiniteField
