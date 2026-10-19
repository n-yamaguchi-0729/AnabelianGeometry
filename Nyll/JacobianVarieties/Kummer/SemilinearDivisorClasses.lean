/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.DivisorClasses
import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear

/-!
# Semilinear transport of divisorial Kummer representatives

The existing action on places and degree-zero divisor classes transports an
actual Kummer unit and its torsion class together.
-/

noncomputable section

namespace AlgebraicCurve.Pic0

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]

/-- The semilinear transform of a Kummer representative represents the
semilinear transform of its actual torsion class. -/
theorem exists_kummerUnit_semilinear
    (n : ℕ+) (g : SemilinearAut K F) (u : kummerUnits K F n) :
    ∃ u' : kummerUnits K F n,
      u'.val = Units.map (SemilinearAut.toRingAut g).toMonoidHom u.val ∧
      Multiplicative.toAdd (kummerClass n u') =
        g • Multiplicative.toAdd (kummerClass n u) := by
  let v := Units.map (SemilinearAut.toRingAut g).toMonoidHom u.val
  have hv (p : Place K F) : p.ord (v : F) = (g⁻¹ • p).ord (u.val : F) := by
    change p.ord (g • (u.val : F)) = _
    simpa only [smul_inv_smul] using SemilinearAut.ord_smul g (g⁻¹ • p) (u.val : F)
  let u' : kummerUnits K F n := ⟨v, fun p => by
    rw [hv]
    exact u.property (g⁻¹ • p)⟩
  refine ⟨u', rfl, ?_⟩
  obtain ⟨D, hD⟩ := Divisor.exists_degZero_ord_eq_mul_of_dvd_ord
    n.ne_zero (Units.ne_zero u.val) u.property
  have hD' (p : Place K F) : p.ord (u'.val : F) =
      (n : ℤ) * (SemilinearAut.degZeroSMulHom g D : Divisor K F) p := by
    change p.ord (v : F) = _
    rw [hv, hD, SemilinearAut.coe_degZeroSMulHom, SemilinearAut.divisor_smul_apply]
  apply Subtype.ext
  rw [SemilinearAut.coe_torsion_smul,
    kummerClass_eq n u' (SemilinearAut.degZeroSMulHom g D) hD',
    kummerClass_eq n u D hD, SemilinearAut.pic0_smul_mk]

end AlgebraicCurve.Pic0
