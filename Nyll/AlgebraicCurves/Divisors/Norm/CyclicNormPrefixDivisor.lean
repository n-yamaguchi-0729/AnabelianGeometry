/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.Maps.Maps
public import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
public import Nyll.AlgebraicCurves.Divisors.Norm.SumGaloisSmulEqPullbackPushforward
public import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalHom
public import Nyll.AlgebraicCurves.Divisors.Semilinear.PullbackSmul
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryCocycle
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Tactic.Abel

/-!
# The divisor vertex of a cyclic norm-prefix cochain

The actual norm divisor `σ⁻¹ C − C + N B` gives a specific vertex
whose coboundary is the divisor of the correction-plus-prefix cochain.
The vertex is a finite orbit sum of `B` minus `σ⁻¹ C`; its degree is
therefore `−degree C` when the original divisor downstairs has degree zero.

All finite sums retain the chosen norm preimage and the chosen generator.
The extension degree may be a proper divisor of the coefficient exponent.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open ClassFieldTower.Cohomology

namespace AlgebraicCurve.Divisor

section NormPrefix

variable {K F L : Type*} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [FiniteDimensional F L] [IsGalois F L] [HasPrincipalDivisors K L]

omit [FiniteDimensional F L] [IsGalois F L] [HasPrincipalDivisors K L] in
/-- The semilinear action of field automorphisms fixing the base field. -/
abbrev action : (L ≃ₐ[F] L) →* SemilinearAut K L :=
  SemilinearAut.ofAlgAut.comp (AlgEquiv.restrictScalarsHom K)

omit [FiniteDimensional F L] [IsGalois F L] [HasPrincipalDivisors K L] in
private theorem orbitSum_coboundary (σ : L ≃ₐ[F] L) (D : Divisor K L) (j : ℕ) :
    ∑ i ∈ Finset.range j, action (K := K) (σ ^ i) •
        (action (K := K) σ • D - D) =
      action (K := K) (σ ^ j) • D - D := by
  calc
    _ = ∑ i ∈ Finset.range j,
        (action (K := K) (σ ^ (i + 1)) • D - action (K := K) (σ ^ i) • D) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_sub, smul_smul, ← map_mul, ← pow_succ]
    _ = _ := by
      simpa only [pow_zero, map_one, one_smul] using
        Finset.sum_range_sub (fun i => action (K := K) (σ ^ i) • D) j

private theorem generatorOrbitSum_eq_pullback (σ : L ≃ₐ[F] L)
    (hσ : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (B : Divisor K L) :
    ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[F] L)), action (K := K) (σ ^ i) • B =
      pullback L (pushforward F B) := by
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ τ : L ≃ₐ[F] L, action (K := K) τ • B :=
      Equiv.sum_comp (finiteCyclicGeneratorPowEquiv σ hσ)
        (fun τ => action (K := K) τ • B)
    _ = _ := sum_galois_smul_eq_pullback_pushforward B

omit [FiniteDimensional F L] [IsGalois F L] [HasPrincipalDivisors K L] in
/-- A weighted orbit divisor, expressed as the negative sum of all
shorter orbit prefixes. Its difference is degree times `B` minus its norm. -/
def cyclicDivisorOrbitPrimitive (σ : L ≃ₐ[F] L) (B : Divisor K L) : Divisor K L :=
  - ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[F] L)),
      ∑ j ∈ Finset.range i, action (K := K) (σ ^ j) • B

/-- The chosen finite orbit primitive has the original norm difference. -/
theorem cyclicDivisorOrbitPrimitive_coboundary (σ : L ≃ₐ[F] L)
    (hσ : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (B : Divisor K L) :
    action (K := K) σ • cyclicDivisorOrbitPrimitive σ B -
        cyclicDivisorOrbitPrimitive σ B =
      Nat.card (L ≃ₐ[F] L) • B - pullback L (pushforward F B) := by
  have hprefix (i : ℕ) :
      action (K := K) σ • (∑ j ∈ Finset.range i, action (K := K) (σ ^ j) • B) -
        (∑ j ∈ Finset.range i, action (K := K) (σ ^ j) • B) =
      action (K := K) (σ ^ i) • B - B := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    calc
      _ = ∑ j ∈ Finset.range i,
          (action (K := K) (σ ^ (j + 1)) • B - action (K := K) (σ ^ j) • B) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_smul, ← map_mul, ← pow_succ']
      _ = _ := by
        simpa only [pow_zero, map_one, one_smul] using
          Finset.sum_range_sub (fun j => action (K := K) (σ ^ j) • B) i
  unfold cyclicDivisorOrbitPrimitive
  rw [smul_neg, Finset.smul_sum, neg_sub_neg]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[F] L)),
        (B - action (K := K) (σ ^ i) • B) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (neg_sub _ _).symm.trans ((congrArg Neg.neg (hprefix i)).trans (neg_sub _ _))
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        generatorOrbitSum_eq_pullback σ hσ]

omit [FiniteDimensional F L] [IsGalois F L] [HasPrincipalDivisors K L] in
/-- The divisor vertex attached to the specified norm-descent witnesses. -/
def cyclicNormDivisorVertex (σ : L ≃ₐ[F] L) (k : ℕ) (B C : Divisor K L) :
    Divisor K L :=
  k • cyclicDivisorOrbitPrimitive σ B - action (K := K) σ⁻¹ • C

/-- The generator difference of the same vertex is the divisor of
the norm preimage minus the scaled original divisor downstairs. -/
theorem cyclicNormDivisorVertex_coboundary
    (σ : L ≃ₐ[F] L) (hσ : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (N k : ℕ) (hN : N = k * Nat.card (L ≃ₐ[F] L))
    (u : Lˣ) (B C : Divisor K L)
    (hdiv : principalHom (K := K) (Additive.ofMul u) =
      action (K := K) σ⁻¹ • C - C + N • B) :
    action (K := K) σ • cyclicNormDivisorVertex σ k B C -
        cyclicNormDivisorVertex σ k B C =
      principalHom (K := K) (Additive.ofMul u) - k • pullback L (pushforward F B) := by
  have hc : action (K := K) σ • (action (K := K) σ⁻¹ • C) = C := by
    rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  unfold cyclicNormDivisorVertex
  rw [smul_sub, smul_comm (action (K := K) σ) k, hc]
  calc
    _ = k • (action (K := K) σ • cyclicDivisorOrbitPrimitive σ B -
          cyclicDivisorOrbitPrimitive σ B) + (action (K := K) σ⁻¹ • C - C) := by
      rw [nsmul_sub]
      abel
    _ = _ := by
      rw [cyclicDivisorOrbitPrimitive_coboundary σ hσ, nsmul_sub,
        smul_smul, ← hN, hdiv]
      abel

/-- Every corrected norm prefix has the difference of the same
explicit divisor vertex. This is the divisor of the retained cochain. -/
theorem cyclicNormPrefix_principalHom
    (σ : L ≃ₐ[F] L) (hσ : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (N k : ℕ) (hN : N = k * Nat.card (L ≃ₐ[F] L))
    (u : Lˣ) (B C : Divisor K L)
    (hdiv : principalHom (K := K) (Additive.ofMul u) =
      action (K := K) σ⁻¹ • C - C + N • B) (j : ℕ) :
    principalHom (K := K)
        (∑ i ∈ Finset.range j, Additive.ofMul (Units.map (σ ^ i).toMonoidHom u)) -
      (k * j) • pullback L (pushforward F B) =
        action (K := K) (σ ^ j) • cyclicNormDivisorVertex σ k B C -
          cyclicNormDivisorVertex σ k B C := by
  have hfixed (τ : L ≃ₐ[F] L) :
      action (K := K) τ • pullback L (pushforward F B) = pullback L (pushforward F B) := by
    have h := SemilinearAut.pullback_smul
      (g := (1 : SemilinearAut K F)) (g' := action (K := K) τ)
      (fun a => τ.commutes a) (pushforward F B)
    simpa only [one_smul] using h.symm
  have hprincipal (i : ℕ) :
      principalHom (K := K) (Additive.ofMul (Units.map (σ ^ i).toMonoidHom u)) =
        action (K := K) (σ ^ i) • principalHom (K := K) (Additive.ofMul u) :=
    principalHom_smul (action (K := K) (σ ^ i)) (Additive.ofMul u)
  rw [map_sum]
  calc
    _ = ∑ i ∈ Finset.range j,
        (action (K := K) (σ ^ i) • principalHom (K := K) (Additive.ofMul u) -
          k • pullback L (pushforward F B)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, smul_smul,
        Nat.mul_comm j k]
      exact congrArg (fun z => z - (k * j) • pullback L (pushforward F B))
        (Finset.sum_congr rfl (fun i _ => hprincipal i))
    _ = ∑ i ∈ Finset.range j, action (K := K) (σ ^ i) •
        (action (K := K) σ • cyclicNormDivisorVertex σ k B C -
          cyclicNormDivisorVertex σ k B C) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [cyclicNormDivisorVertex_coboundary σ hσ N k hN u B C hdiv,
        smul_sub, smul_comm (action (K := K) (σ ^ i)) k, hfixed]
    _ = _ := orbitSum_coboundary σ (cyclicNormDivisorVertex σ k B C) j

end NormPrefix

variable {K F L : Type*} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [FiniteDimensional F L]

/-- The explicit vertex has degree `−degree C`; all orbit correction
terms have degree zero because the original norm divisor does. -/
theorem degree_cyclicNormDivisorVertex
    (σ : L ≃ₐ[F] L) (k : ℕ) (B C : Divisor K L)
    (hB : degree (pushforward F B) = 0) :
    degree (cyclicNormDivisorVertex σ k B C) = -degree C := by
  have hBzero : degree B = 0 := (degree_pushforward B).symm.trans hB
  have hzero : degree (cyclicDivisorOrbitPrimitive σ B) = 0 := by
    simp only [cyclicDivisorOrbitPrimitive, map_neg, map_sum,
      SemilinearAut.degree_smul, hBzero, Finset.sum_const_zero, neg_zero]
  rw [cyclicNormDivisorVertex, map_sub, map_nsmul, hzero, nsmul_zero,
    SemilinearAut.degree_smul, zero_sub]

end AlgebraicCurve.Divisor
