/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Henselian.RootsOfUnity

/-!
# Residue powers determine the prime-to-residue cyclotomic action

The field and integral automorphisms are the same compatible action.
Injectivity of reduction on prime-to-residue roots identifies its field
values with the corresponding powers. Discreteness and Henselianity of the
upstairs valuation are not required.
-/

namespace ValuationSubring

variable {L : Type*} [Field L] (R : ValuationSubring L)

/-- A compatible action inducing a residue power acts by that power on every
root whose order is nonzero in the residue field. -/
theorem cyclotomic_power_of_residue_power
    (τ : R ≃+* R) (σ : L ≃+* L)
    (hσ : ∀ a : R, σ (algebraMap R L a) = algebraMap R L (τ a))
    (q : ℕ) (hres : ∀ a : R,
      IsLocalRing.residue R (τ a) = IsLocalRing.residue R a ^ q)
    (n : ℕ) [NeZero (n : IsLocalRing.ResidueField R)]
    (x : L) (hx : x ^ n = 1) : σ x = x ^ q := by
  have : NeZero n := .of_neZero_natCast (IsLocalRing.ResidueField R)
  have hvalpow : R.valuation x ^ n = 1 := by rw [← map_pow, hx, map_one]
  have hval : R.valuation x = 1 :=
    (pow_eq_one_iff_of_nonneg zero_le (NeZero.ne n)).mp hvalpow
  let a : R := ⟨x, (R.valuation_le_one_iff x).mp hval.le⟩
  have ha : a ^ n = 1 := Subtype.ext hx
  have ht : (τ a) ^ n = 1 := by rw [← map_pow, ha, map_one]
  have hq : (a ^ q) ^ n = 1 := by rw [pow_right_comm, ha, one_pow]
  have heq : rootsOfUnity.mkOfPowEq (τ a) ht = rootsOfUnity.mkOfPowEq (a ^ q) hq := by
    apply R.rootsOfUnityReduction_injective n
    apply rootsOfUnity.coe_injective
    change IsLocalRing.residue R (τ a) = IsLocalRing.residue R (a ^ q)
    rw [map_pow, hres]
  have haeq : τ a = a ^ q :=
    congrArg (fun z : rootsOfUnity n R => ((z : Rˣ) : R)) heq
  calc
    σ x = algebraMap R L (τ a) := hσ a
    _ = algebraMap R L (a ^ q) := congrArg (algebraMap R L) haeq
    _ = x ^ q := map_pow (algebraMap R L) a q

end ValuationSubring
