/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Prime-to-residue-characteristic unit roots in strictly local rings

A residue root of a unit lifts by Hensel's lemma because the derivative of
the power polynomial is a unit. No completeness or finite residue field
hypothesis is needed.
-/

@[expose] public section

namespace HenselianLocalRing

/-- On a Henselian local ring with separably closed residue field,
the nth-power map on units is surjective whenever n is a unit. -/
theorem units_pow_surjective_of_isSepClosed
    (R : Type*) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (n : ℕ) (hn : IsUnit (n : R)) :
    Function.Surjective (fun u : Rˣ => u ^ n) := by
  let k := IsLocalRing.ResidueField R
  let r : R →+* k := IsLocalRing.residue R
  have hnr : IsUnit (n : k) := by
    simpa only [map_natCast] using hn.map r
  have : NeZero (n : k) := ⟨hnr.ne_zero⟩
  have : NeZero n := .of_neZero_natCast k
  intro u
  obtain ⟨a, ha⟩ := IsSepClosed.exists_pow_nat_eq (r (u : R)) n
  have ha0 : a ≠ 0 := by
    intro hz
    rw [hz, zero_pow (NeZero.ne n)] at ha
    exact (u.isUnit.map r).ne_zero ha.symm
  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective a
  have ha₀r : r a₀ = a := ha₀
  have hu₀ : IsUnit a₀ := (IsLocalRing.residue_ne_zero_iff_isUnit a₀).mp (by
    rw [ha₀]
    exact ha0)
  let f : Polynomial R := Polynomial.X ^ n - Polynomial.C (u : R)
  have hroot : f.eval a₀ ∈ IsLocalRing.maximalIdeal R := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change r (f.eval a₀) = 0
    simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, map_sub, map_pow]
    rw [ha₀r, ha, sub_self]
  have hder : IsUnit (f.derivative.eval a₀) := by
    simpa only [f, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_C, sub_zero, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] using
      hn.mul (hu₀.pow (n - 1))
  obtain ⟨b, hb, hba⟩ := HenselianLocalRing.is_henselian f
    (Polynomial.monic_X_pow_sub_C (u : R) (NeZero.ne n)) a₀ hroot hder
  have hbpow : b ^ n = (u : R) := by
    simpa only [f, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using hb
  have hbr : r b = a := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hba
    change r (b - a₀) = 0 at h
    rw [map_sub, ha₀r, sub_eq_zero] at h
    exact h
  have hbu : IsUnit b := (IsLocalRing.residue_ne_zero_iff_isUnit b).mp (by
    change r b ≠ 0
    rw [hbr]
    exact ha0)
  obtain ⟨v, hv⟩ := hbu
  refine ⟨v, Units.ext ?_⟩
  change (v : R) ^ n = (u : R)
  rw [hv]
  exact hbpow

/-- In the fraction field of a strictly Henselian DVR, every unit is an
nth power times an integral power of a chosen uniformizer, when n is a unit.
The ring-unit factor comes from the actual Hensel lifting theorem. -/
theorem fractionUnit_eq_pow_mul_uniformizer_zpow
    (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (n : ℕ) (hn : IsUnit (n : R)) {π : R} (hπ : Irreducible π) (x : Kˣ) :
    ∃ (y : Kˣ) (a : ℤ),
      (x : K) = (y : K) ^ n * (algebraMap R K π) ^ a := by
  obtain ⟨a, u, hx⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ x.ne_zero
  obtain ⟨v, hv⟩ := units_pow_surjective_of_isSepClosed R n hn u
  refine ⟨Units.map (algebraMap R K).toMonoidHom v, a, ?_⟩
  calc
    (x : K) = algebraMap R K (u : R) * (algebraMap R K π) ^ a := by
      simpa only [Units.smul_def, Algebra.smul_def] using hx
    _ = (algebraMap R K (v : R)) ^ n * (algebraMap R K π) ^ a := by
      rw [← map_pow]
      exact congrArg (fun z : R => algebraMap R K z * (algebraMap R K π) ^ a)
        (congrArg Units.val hv).symm
    _ = _ := rfl

end HenselianLocalRing

namespace IsDiscreteValuationRing

/-- A power of an actual DVR uniformizer can be the image of a ring unit
only for exponent zero, also for negative integral exponents. -/
theorem uniformizer_zpow_eq_mappedUnit_exponent_zero
    (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {π : R} (hπ : Irreducible π) (πK : Kˣ)
    (hπK : (πK : K) = algebraMap R K π)
    (a : ℤ) (u : Rˣ)
    (h : πK ^ a = Units.map (algebraMap R K).toMonoidHom u) : a = 0 := by
  have hNat (n : ℕ) (v : Rˣ)
      (hv : πK ^ n = Units.map (algebraMap R K).toMonoidHom v) : n = 0 := by
    have hR : π ^ n = (v : R) := by
      apply IsFractionRing.injective R K
      calc
        algebraMap R K (π ^ n) = (algebraMap R K π) ^ n :=
          map_pow (algebraMap R K) π n
        _ = (πK : K) ^ n := congrArg (fun z : K => z ^ n) hπK.symm
        _ = ((πK ^ n : Kˣ) : K) :=
          (map_pow (Units.coeHom K) πK n).symm
        _ = algebraMap R K (v : R) := congrArg Units.val hv
    have hp : IsUnit (π ^ n) := by
      rw [hR]
      exact v.isUnit
    exact (isUnit_pow_iff_of_not_isUnit hπ.not_isUnit).mp hp
  cases a with
  | ofNat n =>
    change πK ^ (n : ℤ) = Units.map (algebraMap R K).toMonoidHom u at h
    have hn : n = 0 := hNat n u (by simpa only [zpow_natCast] using h)
    rw [hn]
    rfl
  | negSucc n =>
    have hi := congrArg (fun z : Kˣ => z⁻¹) h
    change (πK ^ (-((n + 1 : ℕ) : ℤ)))⁻¹ =
      (Units.map (algebraMap R K).toMonoidHom u)⁻¹ at hi
    have he : πK ^ (n + 1) =
        Units.map (algebraMap R K).toMonoidHom (u⁻¹) := by
      simpa only [zpow_neg, zpow_natCast, inv_inv, map_inv] using hi
    exact False.elim (Nat.succ_ne_zero n (hNat (n + 1) (u⁻¹) he))

/-- The integral exponent in the DVR fraction-field unit/uniformizer
normal form is unique. -/
theorem uniformizer_zpow_eq_unit_mul_zpow_exponent
    (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {π : R} (hπ : Irreducible π) (πK : Kˣ)
    (hπK : (πK : K) = algebraMap R K π)
    (a b : ℤ) (u : Rˣ)
    (h : πK ^ a = Units.map (algebraMap R K).toMonoidHom u * πK ^ b) :
    a = b := by
  have he : πK ^ (a - b) = Units.map (algebraMap R K).toMonoidHom u := by
    rw [zpow_sub, h, mul_assoc, mul_inv_cancel, mul_one]
  exact sub_eq_zero.mp
    (uniformizer_zpow_eq_mappedUnit_exponent_zero R K hπ πK hπK (a - b) u he)

end IsDiscreteValuationRing
