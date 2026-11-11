/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.Maps.Maps
public import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalHom

/-! # Principal divisors under the actual field inclusion -/

@[expose] public section

noncomputable section

namespace AlgebraicCurve.Divisor

/-- Pulling back the principal divisor of the specified unit gives
the principal divisor of that same unit in the extension field. -/
theorem principalHom_map
    {K F L : Type*} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsIntegral F L] [HasPrincipalDivisors K F] [HasPrincipalDivisors K L]
    (u : Additive Fˣ) :
    principalHom (K := K)
        (Additive.ofMul (Units.map (algebraMap F L).toMonoidHom u.toMul)) =
      pullback L (principalHom u) := by
  ext w
  rw [principalHom_apply, pullback_apply, principalHom_apply]
  exact w.ord_restrict (u.toMul : F)

end AlgebraicCurve.Divisor
