/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_ord_algebraMap_eq_mul_ord.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Basic

/-!
# Place exists ord algebra Map eq mul ord
-/

open IsDedekindDomain WithZero IsLocalRing AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.exists_ord_algebraMap_eq_mul_ord {K F F' : Type*} [Field K]
  [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] (w : Place K F') (v : Place K
  F) (hv : v.toValuationSubring = w.toValuationSubring.comap (algebraMap F F')) :
    ∃ e : ℕ, 0 < e ∧ ∀ f : F, w.ord (algebraMap F F' f) = e * v.ord f := by
  have hmem : ∀ {f : F}, f ∈ v.toValuationSubring → algebraMap F F' f ∈ w.toValuationSubring :=
    fun {f} h => by
      rw [hv] at h
      exact (ValuationSubring.mem_comap).mp h
  have hmem' : ∀ {f : F}, algebraMap F F' f ∈ w.toValuationSubring → f ∈ v.toValuationSubring :=
    fun {f} h => by
      rw [hv]
      exact (ValuationSubring.mem_comap).mpr h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπF : (π : F) ≠ 0 := by
    exact fun h => hπ.ne_zero (Subtype.ext h)
  have hπF' : algebraMap F F' (π : F) ≠ 0 := (map_ne_zero (algebraMap F F')).mpr hπF
  have he0 : 0 ≤ w.ord (algebraMap F F' (π : F)) := w.ord_nonneg_of_mem (hmem π.2)
  have hepos : 0 < w.ord (algebraMap F F' (π : F)) := by
    rcases eq_or_lt_of_le he0 with h0 | h
    · exfalso
      have hinv : (algebraMap F F' (π : F))⁻¹ ∈ w.toValuationSubring :=
        w.mem_of_ord_nonneg (inv_ne_zero hπF') (by rw [w.ord_inv, ← h0, neg_zero])
      have hinv' : (π : F)⁻¹ ∈ v.toValuationSubring := hmem' (by rwa [map_inv₀])
      have h1 := v.ord_nonneg_of_mem hinv'
      rw [v.ord_inv, v.ord_coe_irreducible hπ] at h1
      omega
    · exact h
  have hunit : ∀ u : v.toValuationSubringˣ,
      w.ord (algebraMap F F' ((u : v.toValuationSubring) : F)) = 0 := by
    intro u
    have h1 : 0 ≤ w.ord (algebraMap F F' ((u : v.toValuationSubring) : F)) :=
      w.ord_nonneg_of_mem (hmem (u : v.toValuationSubring).2)
    have h2 : 0 ≤ w.ord (algebraMap F F' ((↑(u⁻¹) : v.toValuationSubring) : F)) :=
      w.ord_nonneg_of_mem (hmem (↑(u⁻¹) : v.toValuationSubring).2)
    have hu0 : ((u : v.toValuationSubring) : F) ≠ 0 :=
      fun h => u.ne_zero (Subtype.ext h)
    have hu0' : ((↑(u⁻¹) : v.toValuationSubring) : F) ≠ 0 :=
      fun h => (u⁻¹).ne_zero (Subtype.ext h)
    have hprod : ((u : v.toValuationSubring) : F) * ((↑(u⁻¹) : v.toValuationSubring) : F) = 1 := by
      have := u.mul_inv
      rw [Subtype.ext_iff] at this
      push_cast at this
      exact this
    have hsum : w.ord (algebraMap F F' ((u : v.toValuationSubring) : F))
        + w.ord (algebraMap F F' ((↑(u⁻¹) : v.toValuationSubring) : F)) = 0 := by
      rw [← w.ord_mul ((map_ne_zero (algebraMap F F')).mpr hu0)
        ((map_ne_zero (algebraMap F F')).mpr hu0'), ← map_mul, hprod, map_one, w.ord_one]
    omega
  refine ⟨(w.ord (algebraMap F F' (π : F))).toNat, by omega, fun f => ?_⟩
  rw [Int.toNat_of_nonneg he0]
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, w.ord_zero, v.ord_zero, mul_zero]
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  have hu0 : ((u : v.toValuationSubring) : F) ≠ 0 :=
    fun h => u.ne_zero (Subtype.ext h)
  conv_lhs => rw [hu]
  rw [map_mul, map_zpow₀, w.ord_mul ((map_ne_zero (algebraMap F F')).mpr hu0) (zpow_ne_zero _ hπF'),
    hunit u, zero_add, w.ord_zpow, mul_comm]
