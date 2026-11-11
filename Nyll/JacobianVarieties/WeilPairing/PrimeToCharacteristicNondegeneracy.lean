/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.JacobianVarieties.WeilPairing.DivisorialPairingToHomInjectiveDivisibleCoprime
public import Nyll.JacobianVarieties.Pic0.ZsmulEqFiniteDimensionalRatFunc
public import Nyll.JacobianVarieties.Pic0.DivisorialWeilPairingDataAlgClosed
public import Nyll.AlgebraicCurves.FunctionFields.Rational.FunctionFieldRatFuncAlgHomApplyXEq
public import Nyll.JacobianVarieties.Pic0.TorsionBijectiveInjective
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Nondegeneracy of prime-to-characteristic divisorial Weil pairings

The existing Kummer detection argument uses divisibility over finite
rational-function-field extensions. The actual Jacobian construction supplies
that divisibility over arbitrary algebraically closed constants, so the
exponent need only be invertible in the constants.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve

namespace AlgebraicCurve.DivisorialWeilPairingData

/-- The actual divisorial Weil pairing detects every torsion class when
its exponent is invertible in the algebraically closed field of constants. -/
theorem toHom_injective_of_isUnit
    {K F : Type*} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {n : ℕ} [NeZero n] (hn : IsUnit (n : K))
    (w : DivisorialWeilPairingData K F n) :
    Function.Injective w.toHom := by
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
  apply w.toHom_injective_of_divisible_coprime_of_isAlgClosed
    hn.ne_zero
  intro L _ _ _ _ _
  exact Pic0.exists_zsmul_eq_of_finiteDimensional_ratFunc K L

/-- Finite torsion duality makes the same divisorial pairing perfect. -/
theorem perfect_of_isUnit
    {K F : Type*} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {n : ℕ} [NeZero n] (hn : IsUnit (n : K))
    [Finite (Pic0.torsion K F n)] (w : DivisorialWeilPairingData K F n) :
    w.Perfect := by
  have : NeZero (n : K) := ⟨hn.ne_zero⟩
  exact Pic0.torsion.bijective_of_injective w.toHom (w.toHom_injective_of_isUnit hfg hn)

end AlgebraicCurve.DivisorialWeilPairingData
