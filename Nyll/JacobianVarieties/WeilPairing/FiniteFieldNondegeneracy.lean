/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.JacobianVarieties.WeilPairing.DivisorialPairingToHomInjectiveDivisibleCoprime
public import Nyll.JacobianVarieties.WeilPairing.TransportedDivisorialPairing
public import Nyll.JacobianVarieties.Pic0.ZsmulEqFiniteDimensionalRatFunc
public import Nyll.JacobianVarieties.Pic0.DivisorialWeilPairingDataAlgClosed
public import Nyll.AlgebraicCurves.FunctionFields.Rational.FunctionFieldRatFuncAlgHomApplyXEq
public import Nyll.GaloisCohomology.FieldTheory.FiniteFrobeniusUnits
public import Mathlib.Algebra.CharP.Algebra

/-!
# Prime-to-characteristic Weil nondegeneracy over finite constants

The divisibility input comes from the existing geometric Jacobian theorem.
The required periodicity of algebraic constants follows from actual finite
Frobenius periods. No characteristic-zero hypothesis is used.

-/

@[expose] public section

noncomputable section

open AlgebraicCurve

namespace AlgebraicCurve.DivisorialWeilPairingData

/-- The actual divisorial Weil pairing is nondegenerate at every invertible
exponent over an algebraic closure of finite constants. -/
theorem toHom_injective_finiteField
    (k : Type*) [Field k] [Finite k]
    {K F : Type*} [Field K] [IsAlgClosed K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {n : ℕ} [NeZero n] (hn : (n : K) ≠ 0)
    (w : DivisorialWeilPairingData K F n) : Function.Injective w.toHom := by
  let : Fintype k := Fintype.ofFinite k
  have : CharP K (ringChar k) :=
    charP_of_injective_algebraMap (algebraMap k K).injective (ringChar k)
  have : ExpChar K (ringChar k) := ExpChar.prime (CharP.char_is_prime k (ringChar k))
  have hperiod (a : K) : ∃ r : ℕ, 0 < r ∧ a ^ ringChar k ^ r = a := by
    obtain ⟨d, _, hcard⟩ := FiniteField.card k (ringChar k)
    obtain ⟨r, hr, h⟩ := FiniteField.exists_frobenius_period k K a
    refine ⟨(d : ℕ) * r, Nat.mul_pos d.pos (Nat.pos_of_ne_zero hr), ?_⟩
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
      hcard, ← pow_mul] at h
    exact h
  obtain ⟨x, hx, hfin⟩ := hfg
  have hxrange : x ∉ Set.range (algebraMap K F) := by
    rintro ⟨a, rfl⟩
    exact hx (isAlgebraic_algebraMap a)
  obtain ⟨φ, hφ⟩ := FunctionField.exists_ratFuncAlgHom_apply_X_eq hxrange
  let : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  have : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  have : FiniteDimensional (RatFunc K) F :=
    JacobianVarieties.Pic0.Proofs.ClosedFieldWeilData.AlgebraicCurve.WC7P.finite_ratFunc_of_adjoin
      φ hφ hfin
  apply w.toHom_injective_of_divisible_coprime_of_isAlgClosed hn
  intro L _ _ _ _ _
  exact Pic0.exists_zsmul_eq_of_finiteDimensional_ratFunc_of_forall_pow_eq_self
    K (ringChar k) hperiod L

/-- Transporting the same pairing preserves prime-to-characteristic
nondegeneracy over finite constants. -/
theorem pairingOn_injective_finiteField
    (k : Type*) [Field k] [Finite k]
    {K F B : Type*} [Field K] [IsAlgClosed K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [Field F] [Algebra K F] [HasPrincipalDivisors K F] [AddCommGroup B]
    {n : ℕ} [NeZero n] (w : DivisorialWeilPairingData K F n)
    (e : Pic0.torsion K F n ≃+ B)
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hn : (n : K) ≠ 0) : Function.Injective (w.pairingOn e) := by
  intro a b hab
  apply e.symm.injective
  apply w.toHom_injective_finiteField k hfg hn
  apply Additive.toMul.injective
  ext z
  have h := congrArg (fun χ : Additive (AddChar B K) => Additive.toMul χ (e z)) hab
  simpa only [pairingOn_apply, e.symm_apply_apply, toHom_apply_apply] using h

end AlgebraicCurve.DivisorialWeilPairingData
