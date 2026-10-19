/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Rational.RatFuncRationalPairFunction
import Nyll.AlgebraicCurves.FunctionFields.Constants.RatFuncConstantExtensionOrders
import Nyll.AlgebraicCurves.Places.ValuationRings.EqComapToValuationSubringEq
import Nyll.AlgebraicCurves.Places.Basic

/-! # The same arithmetic function has the prescribed geometric divisor

The function is chosen in k(t), then extended to L(t). Orders at every
geometric place are controlled by unramified constant extension. Uniqueness
of the place above a rational arithmetic place rules out additional support.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open AlgebraicCurve
open scoped RatFunc
attribute [local instance] Polynomial.algebra

namespace AnabelianGeometry.KummerTheory

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

theorem ratFunc_constantExtension_adjoin_base_eq_top :
    IntermediateField.adjoin L
      (Set.range (algebraMap (RatFunc k) (RatFunc L))) = ⊤ := by
  apply top_unique
  rw [← RatFunc.adjoin_X (K := L)]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  have hx' : x = (RatFunc.X : RatFunc L) := Set.mem_singleton_iff.mp hx
  subst x
  exact IntermediateField.subset_adjoin L _
    ⟨RatFunc.X, ratFunc_constantExtension_map_X (k := k) (L := L)⟩

theorem ratFunc_constantExtension_comap_eq_of_ord_eq
    (V : Place k (RatFunc k)) (W : Place L (RatFunc L))
    (hord : ∀ f : RatFunc k,
      W.ord (algebraMap (RatFunc k) (RatFunc L) f) = V.ord f) :
    W.toValuationSubring.comap (algebraMap (RatFunc k) (RatFunc L)) =
      V.toValuationSubring := by
  ext f
  change algebraMap (RatFunc k) (RatFunc L) f ∈ W.toValuationSubring ↔
    f ∈ V.toValuationSubring
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero]
    exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [W.mem_iff_ord_nonneg ((map_ne_zero _).mpr hf),
      V.mem_iff_ord_nonneg hf, hord f]

variable [Algebra.IsAlgebraic k L] [Algebra.IsSeparable k L]

/-- All geometric places have the same normalized order as their arithmetic
restriction. The needed integrality and constants-generation are proved. -/
theorem ratFunc_constantExtension_all_place_orders
    (W : Place L (RatFunc L)) :
    letI : Algebra.IsIntegral (RatFunc k) (RatFunc L) :=
      ratFunc_constantExtension_isIntegral (k := k) (L := L)
    ∀ f : RatFunc k,
      W.ord (algebraMap (RatFunc k) (RatFunc L) f) =
        ((W.forgetConstants (K := k)).restrict (RatFunc k)).ord f := by
  let : Algebra.IsIntegral (RatFunc k) (RatFunc L) :=
    ratFunc_constantExtension_isIntegral (k := k) (L := L)
  intro f
  have he := Place.ramificationIndex_forgetConstants_eq_one_of_adjoin_range_eq_top
    (K := k) (ratFunc_constantExtension_adjoin_eq_top (k := k) (L := L)) W
  have h := (W.forgetConstants (K := k)).ord_restrict (F := RatFunc k) f
  simpa only [Place.ord_forgetConstants, he, Nat.cast_one, one_mul] using h

/-- A nonzero function over k with divisor V₀ - Vinf, together with its full
geometric divisor at specified places W₀ and Winf. No function witness or
absence-of-extra-support premise is assumed. -/
theorem ratFunc_exists_function_geometric_rationalPlace_pair
    (V₀ Vinf : Place k (RatFunc k))
    (hV₀ : V₀.IsRational) (hVinf : Vinf.IsRational)
    (W₀ Winf : Place L (RatFunc L))
    (hW₀ : ∀ f : RatFunc k,
      W₀.ord (algebraMap (RatFunc k) (RatFunc L) f) = V₀.ord f)
    (hWinf : ∀ f : RatFunc k,
      Winf.ord (algebraMap (RatFunc k) (RatFunc L) f) = Vinf.ord f) :
    ∃ f : RatFunc k, f ≠ 0 ∧
      (∀ V : Place k (RatFunc k),
        V.ord f = (if V = V₀ then 1 else 0) - (if V = Vinf then 1 else 0)) ∧
      ∀ W : Place L (RatFunc L),
        W.ord (algebraMap (RatFunc k) (RatFunc L) f) =
          (if W = W₀ then 1 else 0) - (if W = Winf then 1 else 0) := by
  classical
  let : Algebra.IsIntegral (RatFunc k) (RatFunc L) :=
    ratFunc_constantExtension_isIntegral (k := k) (L := L)
  let r : Place L (RatFunc L) → Place k (RatFunc k) :=
    fun W => (W.forgetConstants (K := k)).restrict (RatFunc k)
  have hrestrict (V : Place k (RatFunc k)) (hV : V.IsRational)
      (Wv : Place L (RatFunc L))
      (hWv : ∀ f : RatFunc k,
        Wv.ord (algebraMap (RatFunc k) (RatFunc L) f) = V.ord f)
      (W : Place L (RatFunc L)) : r W = V ↔ W = Wv := by
    have hcomap := ratFunc_constantExtension_comap_eq_of_ord_eq V Wv hWv
    have hRV : r Wv = V := by
      apply Place.ext
      change ((Wv.forgetConstants (K := k)).restrict (RatFunc k)).toValuationSubring = _
      rw [Place.restrict_toValuationSubring, Place.forgetConstants_toValuationSubring]
      exact hcomap
    constructor
    · intro h
      apply Place.eq_of_comap_toValuationSubring_eq_of_isRational
        (ratFunc_constantExtension_adjoin_base_eq_top (k := k) (L := L)) V hV W Wv
        _ hcomap
      have h' := congrArg Place.toValuationSubring h
      change ((W.forgetConstants (K := k)).restrict (RatFunc k)).toValuationSubring = _ at h'
      rw [Place.restrict_toValuationSubring, Place.forgetConstants_toValuationSubring] at h'
      exact h'
    · rintro rfl
      exact hRV
  obtain ⟨f, hf, hord⟩ := ratFunc_exists_function_rationalPlace_pair V₀ Vinf hV₀ hVinf
  refine ⟨f, hf, hord, fun W => ?_⟩
  have hW : W.ord (algebraMap (RatFunc k) (RatFunc L) f) = (r W).ord f :=
    ratFunc_constantExtension_all_place_orders (k := k) W f
  rw [hW, hord, hrestrict V₀ hV₀ W₀ hW₀ W, hrestrict Vinf hVinf Winf hWinf W]

end AnabelianGeometry.KummerTheory
