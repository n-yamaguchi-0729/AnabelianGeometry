/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.JacobianVarieties.WeilPairing.PrimeToCharacteristicNondegeneracy

/-!
# Nondegeneracy of the divisorial Weil pairing in characteristic zero

The divisibility input in the existing Kummer detection proof is supplied
by the proved geometric Jacobian construction and multiplication
surjectivity, for every finite rational-function-field extension.
No divisibility or nondegeneracy hypothesis is left to the caller.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve

namespace AlgebraicCurve.DivisorialWeilPairingData

/-- In characteristic zero the actual divisorial Weil pairing is
nondegenerate. The auxiliary divisibility of Picard groups is proved by
the existing Jacobian construction, rather than assumed. -/
theorem toHom_injective_charZero
    {K F : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {n : ℕ} [NeZero n] (w : DivisorialWeilPairingData K F n) :
    Function.Injective w.toHom :=
  w.toHom_injective_of_isUnit hfg (isUnit_iff_ne_zero.mpr
    (Nat.cast_ne_zero.mpr (NeZero.ne n)))

end AlgebraicCurve.DivisorialWeilPairingData
