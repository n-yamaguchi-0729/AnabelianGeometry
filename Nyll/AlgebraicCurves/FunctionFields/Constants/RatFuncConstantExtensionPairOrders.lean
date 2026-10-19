/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Constants.RatFuncRationalPairConstantExtension

/-! # Constant extension preserves the divisor of the same pair function

The function is an input, rather than a newly chosen witness. Over an algebraic
separable constant extension its orders at all places are determined by its
arithmetic orders. Rationality of the two arithmetic places identifies their
unique extensions and excludes additional support.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open AlgebraicCurve
open scoped RatFunc
attribute [local instance] Polynomial.algebra

namespace AnabelianGeometry.KummerTheory

variable {k E : Type*} [Field k] [Field E] [Algebra k E]
variable [Algebra.IsAlgebraic k E] [Algebra.IsSeparable k E]

/-- The already chosen function retains its full pair-order formula after
an algebraic separable extension of constants. -/
theorem ratFunc_constantExtension_pair_orders
    (V₀ Vinf : Place k (RatFunc k))
    (hV₀ : V₀.IsRational) (hVinf : Vinf.IsRational)
    (W₀ Winf : Place E (RatFunc E))
    (hW₀ : ∀ z : RatFunc k,
      W₀.ord (algebraMap (RatFunc k) (RatFunc E) z) = V₀.ord z)
    (hWinf : ∀ z : RatFunc k,
      Winf.ord (algebraMap (RatFunc k) (RatFunc E) z) = Vinf.ord z)
    (f : RatFunc k)
    (harith : ∀ V : Place k (RatFunc k),
      V.ord f = (if V = V₀ then 1 else 0) - (if V = Vinf then 1 else 0)) :
    ∀ W : Place E (RatFunc E),
      W.ord (algebraMap (RatFunc k) (RatFunc E) f) =
        (if W = W₀ then 1 else 0) - (if W = Winf then 1 else 0) := by
  classical
  let : Algebra.IsIntegral (RatFunc k) (RatFunc E) :=
    ratFunc_constantExtension_isIntegral (k := k) (L := E)
  let r : Place E (RatFunc E) → Place k (RatFunc k) :=
    fun W => (W.forgetConstants (K := k)).restrict (RatFunc k)
  have hrestrict (V : Place k (RatFunc k)) (hV : V.IsRational)
      (Wv : Place E (RatFunc E))
      (hWv : ∀ z : RatFunc k,
        Wv.ord (algebraMap (RatFunc k) (RatFunc E) z) = V.ord z)
      (W : Place E (RatFunc E)) : r W = V ↔ W = Wv := by
    have hcomap := ratFunc_constantExtension_comap_eq_of_ord_eq V Wv hWv
    have hRV : r Wv = V := by
      apply Place.ext
      change ((Wv.forgetConstants (K := k)).restrict (RatFunc k)).toValuationSubring = _
      rw [Place.restrict_toValuationSubring, Place.forgetConstants_toValuationSubring]
      exact hcomap
    constructor
    · intro h
      apply Place.eq_of_comap_toValuationSubring_eq_of_isRational
        (ratFunc_constantExtension_adjoin_base_eq_top (k := k) (L := E)) V hV W Wv
        _ hcomap
      have h' := congrArg Place.toValuationSubring h
      change ((W.forgetConstants (K := k)).restrict (RatFunc k)).toValuationSubring = _ at h'
      rw [Place.restrict_toValuationSubring, Place.forgetConstants_toValuationSubring] at h'
      exact h'
    · rintro rfl
      exact hRV
  intro W
  have hW : W.ord (algebraMap (RatFunc k) (RatFunc E) f) = (r W).ord f :=
    ratFunc_constantExtension_all_place_orders (k := k) W f
  rw [hW, harith, hrestrict V₀ hV₀ W₀ hW₀ W, hrestrict Vinf hVinf Winf hWinf W]

end AnabelianGeometry.KummerTheory
