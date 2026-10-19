/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.RatFuncSquareClasses
import Nyll.AlgebraicCurves.Places.Rational.FiniteOrder

/-! # Polynomial multiplicities are the actual finite-place orders -/

noncomputable section
open Polynomial UniqueFactorizationMonoid AlgebraicCurve

namespace AnabelianGeometry.KummerTheory

variable {k : Type*} [Field k]

local instance : DecidableEq k := Classical.decEq k

/-- Actual finite-place order of a polynomial equals its prime multiplicity. -/
theorem finitePlace_ord_polynomial_eq_multiplicity {P : k[X]} (hP : Irreducible P)
    (q : k[X]) (hq : q ≠ 0) :
    (RationalFunctionField.finitePlace k hP).ord (algebraMap k[X] (RatFunc k) q) =
      (multiplicity P q : ℤ) := by
  let v := RationalFunctionField.finitePlace k hP
  let n := multiplicity P q
  have hfin : FiniteMultiplicity P q := FiniteMultiplicity.of_not_isUnit hP.not_isUnit hq
  obtain ⟨r, hr, hnr⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  change q = P ^ n * r at hr
  have hr0 : r ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hr
    exact hq hr
  have hmapP : algebraMap k[X] (RatFunc k) P ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hP.ne_zero
  have hmapr : algebraMap k[X] (RatFunc k) r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hr0
  have hPord : v.ord (algebraMap k[X] (RatFunc k) P) = 1 :=
    RationalFunctionField.ord_ofHeightOneSpectrum_of_span
      (RationalFunctionField.heightOneSpectrumOfIrreducible k hP) hP.ne_zero rfl
  have hrord : v.ord (algebraMap k[X] (RatFunc k) r) = 0 := by
    by_contra hne
    have hmem := (Place.ord_ofHeightOneSpectrum_ne_zero_iff
      (K := k) (F := RatFunc k)
      (RationalFunctionField.heightOneSpectrumOfIrreducible k hP) hr0).mp hne
    change r ∈ Ideal.span ({P} : Set k[X]) at hmem
    exact hnr (Ideal.mem_span_singleton.mp hmem)
  change v.ord (algebraMap k[X] (RatFunc k) q) = (n : ℤ)
  rw [hr, map_mul, map_pow, v.ord_mul (pow_ne_zero n hmapP) hmapr]
  rw [← zpow_natCast, v.ord_zpow, hPord, hrord, mul_one, add_zero]

/-- The integer factor-count difference equals the actual normalized order. -/
theorem finitePlace_ord_eq_rationalPrimeOrder {P : k[X]} (hP : Irreducible P)
    (f : RatFunc k) (hf : f ≠ 0) :
    (RationalFunctionField.finitePlace k hP).ord f = rationalPrimeOrder P f := by
  let v := RationalFunctionField.finitePlace k hP
  have hn : algebraMap k[X] (RatFunc k) f.num ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr
      (RatFunc.num_ne_zero hf)
  have hd : algebraMap k[X] (RatFunc k) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr
      (RatFunc.denom_ne_zero f)
  calc
    v.ord f = v.ord (algebraMap k[X] (RatFunc k) f.num /
        algebraMap k[X] (RatFunc k) f.denom) :=
      congrArg v.ord (RatFunc.num_div_denom f).symm
    _ = v.ord (algebraMap k[X] (RatFunc k) f.num) -
        v.ord (algebraMap k[X] (RatFunc k) f.denom) := by
      rw [div_eq_mul_inv, v.ord_mul hn (inv_ne_zero hd), v.ord_inv, sub_eq_add_neg]
    _ = rationalPrimeOrder P f := by
      rw [finitePlace_ord_polynomial_eq_multiplicity hP f.num (RatFunc.num_ne_zero hf),
        finitePlace_ord_polynomial_eq_multiplicity hP f.denom (RatFunc.denom_ne_zero f)]
      simp only [rationalPrimeOrder,
        multiplicity_eq_count_normalizedFactors hP (RatFunc.num_ne_zero hf),
        multiplicity_eq_count_normalizedFactors hP (RatFunc.denom_ne_zero f)]

/-- All finite actual place orders recover the square class relative to a coordinate. -/
theorem ratFunc_eq_constant_mul_coordinate_mul_sq_of_even_orders
    (f t : RatFunc k) (hf : f ≠ 0) (ht : t ≠ 0)
    (h : ∀ (P : k[X]) (hP : Irreducible P),
      (2 : ℤ) ∣ (RationalFunctionField.finitePlace k hP).ord (f / t)) :
    ∃ (c : kˣ) (s : RatFunc k), f = algebraMap k (RatFunc k) (c : k) * t * s ^ 2 := by
  apply ratFunc_eq_constant_mul_coordinate_mul_sq f t hf ht
  intro P hP
  rw [← finitePlace_ord_eq_rationalPrimeOrder hP (f / t) (div_ne_zero hf ht)]
  exact h P hP

end AnabelianGeometry.KummerTheory
