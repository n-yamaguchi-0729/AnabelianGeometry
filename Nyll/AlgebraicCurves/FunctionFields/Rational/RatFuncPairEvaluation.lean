/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Places.Rational.RatFuncAlgebraMapOrdEqZero
import Nyll.AlgebraicCurves.Places.Evaluation.EvalAtCongr
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.SchemeTheory.FunctionFields.RatFuncAlgEquivApplyXEqMoebius
import Nyll.AlgebraicCurves.FunctionFields.Rational.RatFuncPairFunctionCoordinate

/-! # Evaluation of the unchanged pair function in its normalized coordinate

Functions with the same full divisor differ by a constant. Their ratios of
values therefore agree, including evaluation at their common zero. Separately,
the existing coordinate for a specified function can be normalized by its own
actual nonzero value at a third rational place; the resulting formula is the
literal quotient of that original function, rather than another divisor choice.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open AlgebraicCurve

namespace AnabelianGeometry.KummerTheory

variable {k : Type*} [Field k]

/-- Equality of all orders determines the nonzero functions up to one constant. -/
theorem ratFunc_eq_constant_mul_of_same_orders
    (f g : RatFunc k) (hf : f ≠ 0) (hg : g ≠ 0)
    (horders : ∀ V : Place k (RatFunc k), V.ord f = V.ord g) :
    ∃ c : k, c ≠ 0 ∧ f = algebraMap k (RatFunc k) c * g := by
  obtain ⟨c, hc, hfg⟩ :=
    RationalFunctionField.exists_algebraMap_of_forall_ord_eq_zero (div_ne_zero hf hg)
      (fun V => by
        rw [div_eq_mul_inv, V.ord_mul hf (inv_ne_zero hg), V.ord_inv, horders V,
          add_neg_cancel])
  exact ⟨c, hc, (div_eq_iff hg).mp hfg⟩

/-- The normalized value ratio is independent of the principal-divisor witness.
The original f is retained on the left; g may be the explicit bracket function. -/
theorem ratFunc_evalAt_ratio_eq_of_same_orders
    (f g : RatFunc k) (hf : f ≠ 0) (hg : g ≠ 0)
    (horders : ∀ V : Place k (RatFunc k), V.ord f = V.ord g)
    (Vc Vd : Place k (RatFunc k)) (hc : Vc.IsRational) (hd : Vd.IsRational)
    (hgc : 0 ≤ Vc.ord g) (hgd : 0 ≤ Vd.ord g) :
    Vd.evalAt f / Vc.evalAt f = Vd.evalAt g / Vc.evalAt g := by
  obtain ⟨c, hc0, hfg⟩ := ratFunc_eq_constant_mul_of_same_orders f g hf hg horders
  have heval (V : Place k (RatFunc k)) (hV : V.IsRational) (hreg : 0 ≤ V.ord g) :
      V.evalAt f = c * V.evalAt g := by
    rw [hfg, V.evalAt_mul hV (V.algebraMap_mem' c) (V.mem_of_ord_nonneg hg hreg),
      V.evalAt_algebraMap]
  rw [heval Vd hd hgd, heval Vc hc hgc]
  exact mul_div_mul_left _ _ hc0

/-- Evaluation of literal normalization by a base-field scalar. -/
theorem ratFunc_evalAt_div_constant
    (V : Place k (RatFunc k)) (hV : V.IsRational)
    (f : RatFunc k) (hf : f ≠ 0) (hreg : 0 ≤ V.ord f) (c : k) :
    V.evalAt (f / algebraMap k (RatFunc k) c) = V.evalAt f / c := by
  rw [div_eq_mul_inv, ← map_inv₀,
    V.evalAt_mul hV (V.mem_of_ord_nonneg hf hreg) (V.algebraMap_mem' c⁻¹),
    V.evalAt_algebraMap, div_eq_mul_inv]

/-- Scaling the coordinate by a nonzero constant keeps the specified function
literal: no new function is selected by a principal-divisor existence theorem. -/
theorem ratFunc_exists_normalized_coordinate
    (e : RatFunc k ≃ₐ[k] RatFunc k) (f : RatFunc k) (he : e RatFunc.X = f)
    (c : k) (hc : c ≠ 0) :
    ∃ e' : RatFunc k ≃ₐ[k] RatFunc k,
      e' RatFunc.X = f / algebraMap k (RatFunc k) c := by
  obtain ⟨s, hs⟩ := RatFunc.exists_algEquiv_apply_X_eq_moebius c⁻¹ 0 0 1
    (by simpa only [mul_one, zero_mul, sub_zero] using inv_ne_zero hc)
  refine ⟨s.trans e, ?_⟩
  change e (s RatFunc.X) = _
  rw [hs]
  simp only [map_zero, map_one, zero_mul, add_zero, zero_add, div_one]
  rw [map_mul, ← RatFunc.algebraMap_eq_C, e.commutes, he, map_inv₀,
    div_eq_mul_inv, mul_comm]

/-- The actual evaluation at a positive-order zero is zero. -/
theorem ratFunc_evalAt_eq_zero_of_ord_pos
    (V : Place k (RatFunc k)) (f : RatFunc k) (hf : f ≠ 0)
    (hpos : 0 < V.ord f) : V.evalAt f = 0 := by
  have heval := V.evalAt_congr (V.mem_of_ord_nonneg hf hpos.le)
    (zero_mem V.toValuationSubring) (Or.inr (by simpa only [sub_zero] using hpos))
  exact heval.trans (by simpa only [map_zero] using V.evalAt_algebraMap (0 : k))

/-- A pair coordinate normalized by the same third-place value sends the original
zero to zero, the third place to one, and every regular place to the actual ratio. -/
theorem ratFunc_pair_coordinate_normalized_values
    (V₀ Vinf Vc : Place k (RatFunc k))
    (hV₀ : V₀.IsRational) (hVinf : Vinf.IsRational) (hVc : Vc.IsRational)
    (hne : V₀ ≠ Vinf) (hc₀ : Vc ≠ V₀) (hcinf : Vc ≠ Vinf)
    (f : RatFunc k) (hf : f ≠ 0)
    (hord : ∀ V : Place k (RatFunc k),
      V.ord f = (if V = V₀ then 1 else 0) - (if V = Vinf then 1 else 0)) :
    Vc.ord f = 0 ∧ Vc.evalAt f ≠ 0 ∧
    ∃ e : RatFunc k ≃ₐ[k] RatFunc k,
      e RatFunc.X = f / algebraMap k (RatFunc k) (Vc.evalAt f) ∧
      V₀.evalAt (e RatFunc.X) = 0 ∧ Vc.evalAt (e RatFunc.X) = 1 ∧
      ∀ V : Place k (RatFunc k), V.IsRational → V ≠ Vinf →
        V.evalAt (e RatFunc.X) = V.evalAt f / Vc.evalAt f := by
  classical
  have hzero : V₀.ord f = 1 := by
    rw [hord, ite_eq_left rfl, ite_eq_right hne, sub_zero]
  have hthird : Vc.ord f = 0 := by
    rw [hord, ite_eq_right hc₀, ite_eq_right hcinf, sub_self]
  have hvalue : Vc.evalAt f ≠ 0 := Vc.evalAt_ne_zero hVc hf hthird
  obtain ⟨e₀, he₀⟩ :=
    ratFunc_exists_algEquiv_apply_X_of_pair_orders V₀ Vinf hVinf hne f hord
  obtain ⟨e, he⟩ := ratFunc_exists_normalized_coordinate e₀ f he₀ (Vc.evalAt f) hvalue
  refine ⟨hthird, hvalue, e, he, ?_, ?_, ?_⟩
  · rw [he, ratFunc_evalAt_div_constant V₀ hV₀ f hf (by omega),
      ratFunc_evalAt_eq_zero_of_ord_pos V₀ f hf (by omega), zero_div]
  · rw [he, ratFunc_evalAt_div_constant Vc hVc f hf hthird.ge, div_self hvalue]
  · intro V hV hVinf'
    rw [he]
    apply ratFunc_evalAt_div_constant V hV f hf ?_ (Vc.evalAt f)
    rw [hord, ite_eq_right hVinf', sub_zero]
    split_ifs <;> omega

end AnabelianGeometry.KummerTheory
