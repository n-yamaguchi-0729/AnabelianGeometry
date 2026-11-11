/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.KummerRootEvaluation
public import Nyll.AlgebraicCurves.Divisors.Maps.Maps
public import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
public import Nyll.AlgebraicCurves.Divisors.Norm.CyclicNormPrefixDivisor
public import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalHom
public import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalPullback
public import Nyll.AlgebraicCurves.Divisors.Semilinear.PullbackSmul
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryPrimitive
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryCocycle
public import Mathlib.Tactic.Ring

/-!
# The divisor of the actual corrected norm cochain

The specified second Kummer root has divisor equal to the pullback of
the second divisor. Its correction cancels the corresponding term in
the original norm prefix. The remaining divisor is exactly the deck
difference of the same explicit cyclic vertex, after field extension.
-/

@[expose] public section

universe u

noncomputable section

open ClassFieldTower.Cohomology
open scoped BigOperators IsMulCommutative

namespace AlgebraicCurve.Divisor

variable {K F E : Type u} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [IsGalois F E] [IsMulCommutative Gal(E/F)]
  [HasPrincipalDivisors K E]

/-- The actual prefix cochain retains the divisor of the original
norm preimage and the original cyclic vertex. -/
theorem cyclicNormPrefixCochain_principalHom
    (g : Gal(E/F)) (hg : ∀ τ : Gal(E/F), τ ∈ Subgroup.zpowers g)
    (N k : ℕ) (hN : N = k * Nat.card Gal(E/F))
    (u : Eˣ) (B C : Divisor K E)
    (hdiv : principalHom (K := K) (Additive.ofMul u) =
      SemilinearAut.ofAlgAut (g.symm.restrictScalars K) • C - C + N • B)
    (τ : Gal(E/F)) :
    principalHom (K := K)
        (finiteCyclicNormPrefixCochain (Rep.ofAlgebraAutOnUnits F E) g hg
          (Additive.ofMul u) τ) -
        (k * (finiteCyclicGeneratorCoordinate g hg τ).val) • pullback E (pushforward F B) =
      SemilinearAut.ofAlgAut (τ.restrictScalars K) • cyclicNormDivisorVertex g k B C -
        cyclicNormDivisorVertex g k B C := by
  have hp := cyclicNormPrefix_principalHom g hg N k hN u B C hdiv
    (finiteCyclicGeneratorCoordinate g hg τ).val
  rw [finiteCyclicGenerator_zpow_coordinate] at hp
  let unitsEquiv : (Rep.ofAlgebraAutOnUnits F E) ≃+ Additive Eˣ := Rep.toAdditive
  change principalHom (K := K)
      (unitsEquiv
        (finiteCyclicNormPrefixCochain (Rep.ofAlgebraAutOnUnits F E) g hg
          (unitsEquiv.symm (Additive.ofMul u)) τ)) -
      (k * (finiteCyclicGeneratorCoordinate g hg τ).val) •
        pullback E (pushforward F B) = _
  rw [finiteCyclicNormPrefixCochain_apply]
  exact hp

/-- The complete cup primitive has the actual deck difference of
the pulled-back cyclic vertex as its divisor. Both the radical root
and the norm preimage remain the specified original elements. -/
theorem cyclicNormCupCochain_principalHom
    {L : Type u} [Field L] [Algebra K L] [Algebra F L] [Algebra E L]
    [IsScalarTower K F L] [IsScalarTower K E L] [IsScalarTower F E L]
    [Algebra.IsIntegral E L] [HasPrincipalDivisors K L]
    (g : Gal(E/F)) (hg : ∀ τ : Gal(E/F), τ ∈ Subgroup.zpowers g)
    (N k : ℕ) [NeZero N] (hN : N = k * Nat.card Gal(E/F))
    (u : Eˣ) (B C : Divisor K E)
    (hdiv : principalHom (K := K) (Additive.ofMul u) =
      SemilinearAut.ofAlgAut (g.symm.restrictScalars K) • C - C + N • B)
    (D : Divisor K F) (hB : pushforward F B = D)
    (f : F) (hf : ∀ v : Place K F, v.ord f = N * D v)
    (β : Lˣ) (hβ : (β : L) ^ N = algebraMap F L f)
    (σ : Gal(L/F)) (τ : Gal(E/F))
    (hτ : ∀ x : E, σ (algebraMap E L x) = algebraMap E L (τ x)) :
    principalHom (K := K)
        (-((k * (finiteCyclicGeneratorCoordinate g hg τ).val) • Additive.ofMul β) +
          Additive.ofMul (Units.map (algebraMap E L).toMonoidHom
            (finiteCyclicNormPrefixCochain (Rep.ofAlgebraAutOnUnits F E) g hg
              (Additive.ofMul u) τ).toMul)) =
      SemilinearAut.ofAlgAut (σ.restrictScalars K) •
          pullback L (cyclicNormDivisorVertex g k B C) -
        pullback L (cyclicNormDivisorVertex g k B C) := by
  have hfE (v : Place K E) : v.ord (algebraMap F E f) = N * pullback E D v := by
    rw [Place.ord_restrict, hf, pullback_apply]
    ring
  have hβE : (β : L) ^ N = algebraMap E L (algebraMap F E f) := by
    rw [← IsScalarTower.algebraMap_apply F E L, hβ]
  have hroot : principalHom (K := K) (Additive.ofMul β) =
      pullback L (pullback E D) := by
    ext w
    rw [principalHom_apply]
    exact ord_eq_pullback_of_pow_eq_algebraMap hfE hβE w
  let unitsEquiv : (Rep.ofAlgebraAutOnUnits F E) ≃+ Additive Eˣ := Rep.toAdditive
  let normPrefix : Additive Eˣ := unitsEquiv
    (finiteCyclicNormPrefixCochain (Rep.ofAlgebraAutOnUnits F E) g hg
      (unitsEquiv.symm (Additive.ofMul u)) τ)
  have hp := congrArg (pullback L)
    (cyclicNormPrefixCochain_principalHom g hg N k hN u B C hdiv τ)
  change pullback L (principalHom (K := K) normPrefix -
    (k * (finiteCyclicGeneratorCoordinate g hg τ).val) •
      pullback E (pushforward F B)) = _ at hp
  rw [map_sub, map_nsmul, hB, map_sub] at hp
  have hintertwines : SemilinearAut.IntertwinesAlong (algebraMap E L)
      (SemilinearAut.ofAlgAut (τ.restrictScalars K))
      (SemilinearAut.ofAlgAut (σ.restrictScalars K)) := hτ
  rw [SemilinearAut.pullback_smul hintertwines] at hp
  change principalHom (K := K)
      (-((k * (finiteCyclicGeneratorCoordinate g hg τ).val) • Additive.ofMul β) +
        Additive.ofMul (Units.map (algebraMap E L).toMonoidHom normPrefix.toMul)) = _
  rw [map_add, map_neg, map_nsmul, hroot, principalHom_map]
  exact (neg_add_eq_sub _ _).trans hp

end AlgebraicCurve.Divisor
