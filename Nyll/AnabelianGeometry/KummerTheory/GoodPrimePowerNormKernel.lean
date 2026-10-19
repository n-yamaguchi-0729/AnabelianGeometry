/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.GoodPrimePowerUnitNormalForm
import Nyll.AnabelianGeometry.KummerTheory.PrimePowerNormKernel
import Nyll.AnabelianGeometry.KummerTheory.CyclotomicNormKernelUnit

/-! # The full norm kernel for every good prime-power unit -/

namespace AnabelianGeometry.KummerTheory

/-- The norm has length equal to the actual unit's order. -/
theorem geomSum_orderOf_goodPrimePowerUnit_mul_eq_zero_iff
    {p r : ℕ} (hp : p.Prime)
    (u : (ZMod (p ^ r))ˣ)
    (hgood : p = 2 → (4 : ℤ) ∣ (((u : ZMod (p ^ r)).val : ℤ) - 1))
    (t : ZMod (p ^ r)) :
    ((∑ j ∈ Finset.range (orderOf u), (u : ZMod (p ^ r)) ^ j) * t = 0) ↔
      ∃ y : ZMod (p ^ r), ((u : ZMod (p ^ r)) - 1) * y = t := by
  by_cases hr0 : r = 0
  · subst r
    let : Subsingleton (ZMod (p ^ 0)) := by
      simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
    constructor
    · intro _
      exact ⟨0, Subsingleton.elim _ _⟩
    · intro _
      exact Subsingleton.elim _ _
  have hr : 0 < r := Nat.pos_of_ne_zero hr0
  rcases goodPrimePowerUnit_normalForm hp hr u hgood with huone | hunit | hprincipal
  · subst u
    simp [eq_comm]
  · have hupow : (u : ZMod (p ^ r)) ^ orderOf u = 1 := by
      calc
        (u : ZMod (p ^ r)) ^ orderOf u =
            (Units.coeHom (ZMod (p ^ r))) (u ^ orderOf u) :=
          ((Units.coeHom (ZMod (p ^ r))).map_pow u (orderOf u)).symm
        _ = 1 := congrArg (Units.coeHom (ZMod (p ^ r))) (pow_orderOf_eq_one u)
    exact geomSum_mul_eq_zero_iff_of_isUnit_sub_one
      (u : ZMod (p ^ r)) (orderOf u) hupow hunit t
  · obtain ⟨s, a, hs, hsr, ha, hu, hps⟩ := hprincipal
    obtain ⟨k, hrk⟩ : ∃ k : ℕ, r = k + s :=
      ⟨r - s, (Nat.sub_add_cancel hsr.le).symm⟩
    subst r
    have horderPrincipal :
        orderOf (1 + (p : ZMod (p ^ (k + s))) ^ s * a) = p ^ k :=
      ZMod.orderOf_one_add_mul_prime_pow hp s hs.ne' hps a ha k
    have horder : orderOf u = p ^ k := by
      rw [← orderOf_injective _ Units.coeHom_injective u, Units.coeHom_apply, hu]
      exact horderPrincipal
    have hkernel := geomSum_principalUnit_mul_eq_zero_iff hp s hs.ne' hps a ha k
    simpa only [horder, hu] using hkernel t

end AnabelianGeometry.KummerTheory
