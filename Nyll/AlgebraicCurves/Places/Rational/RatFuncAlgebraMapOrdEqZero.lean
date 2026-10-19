/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_exists_algebraMap_of_forall_ord_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Lean.Elab.Tactic.Omega

/-!
# Rational functions with zero order at every place
-/

open Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem AlgebraicCurve.RationalFunctionField.exists_algebraMap_of_forall_ord_eq_zero {K :
  Type*} [Field K] {g : RatFunc K} (hg : g ≠ 0) (h : ∀ v : Place K (RatFunc K), v.ord g = 0) :
  ∃ c : K, c ≠ 0 ∧ g = algebraMap K (RatFunc K) c := by
  have hnum0 : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hden0 : g.denom ≠ 0 := g.denom_ne_zero
  have hnum0' : algebraMap K[X] (RatFunc K) g.num ≠ 0 := RatFunc.algebraMap_ne_zero hnum0
  have hden0' : algebraMap K[X] (RatFunc K) g.denom ≠ 0 := RatFunc.algebraMap_ne_zero hden0
  have hsplit : g = algebraMap K[X] (RatFunc K) g.num
      * (algebraMap K[X] (RatFunc K) g.denom)⁻¹ := by
    rw [← div_eq_mul_inv, g.num_div_denom]
  have hkey : ∀ p : K[X], Irreducible p → ¬p ∣ g.num ∧ ¬p ∣ g.denom := by
    intro p hpirr
    have hord : (finitePlace K hpirr).ord (algebraMap K[X] (RatFunc K) g.num)
        = (finitePlace K hpirr).ord (algebraMap K[X] (RatFunc K) g.denom) := by
      have h0 := h (finitePlace K hpirr)
      rw [hsplit, (finitePlace K hpirr).ord_mul hnum0' (inv_ne_zero hden0'),
        Place.ord_inv] at h0
      omega
    constructor
    · intro hdvd
      refine hpirr.not_isUnit (g.isCoprime_num_denom.isUnit_of_dvd' hdvd ?_)
      refine (ord_finitePlace_ne_zero_iff K hpirr hden0).mp ?_
      rw [← hord]
      exact (ord_finitePlace_ne_zero_iff K hpirr hnum0).mpr hdvd
    · intro hdvd
      refine hpirr.not_isUnit (g.isCoprime_num_denom.isUnit_of_dvd' ?_ hdvd)
      refine (ord_finitePlace_ne_zero_iff K hpirr hnum0).mp ?_
      rw [hord]
      exact (ord_finitePlace_ne_zero_iff K hpirr hden0).mpr hdvd
  have hunit : ∀ q : K[X], q ≠ 0 → (∀ p : K[X], Irreducible p → ¬p ∣ q) → IsUnit q := by
    intro q hq hp
    by_contra hu
    obtain ⟨p, hpirr, hpdvd⟩ := WfDvdMonoid.exists_irreducible_factor hu hq
    exact hp p hpirr hpdvd
  obtain ⟨c₁, hc₁u, hc₁⟩ :=
    Polynomial.isUnit_iff.mp (hunit g.num hnum0 fun p hp => (hkey p hp).1)
  obtain ⟨c₂, hc₂u, hc₂⟩ :=
    Polynomial.isUnit_iff.mp (hunit g.denom hden0 fun p hp => (hkey p hp).2)
  have hc₁0 : c₁ ≠ 0 := fun h0 => hnum0 (by rw [← hc₁, h0, map_zero])
  have hc₂0 : c₂ ≠ 0 := fun h0 => hden0 (by rw [← hc₂, h0, map_zero])
  refine ⟨c₁ / c₂, div_ne_zero hc₁0 hc₂0, ?_⟩
  rw [← g.num_div_denom, ← hc₁, ← hc₂, RatFunc.algebraMap_C, RatFunc.algebraMap_C,
    map_div₀, RatFunc.algebraMap_eq_C]
