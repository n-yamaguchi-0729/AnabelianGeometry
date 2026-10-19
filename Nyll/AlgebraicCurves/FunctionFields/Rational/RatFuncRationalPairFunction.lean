/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Rational.RatFuncPrincipalDegreeEqZero
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.AlgebraicCurves.Places.Orders.TranscendentalOrdNeZero

/-! # A rational function for two rational arithmetic places

The degree-zero divisor on k(t) is principal over k itself. This does not
assume k is algebraically closed and does not postulate a function witness.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open AlgebraicCurve

namespace AnabelianGeometry.KummerTheory

theorem ratFunc_exists_function_rationalPlace_pair
    {k : Type*} [Field k]
    (V₀ Vinf : Place k (RatFunc k))
    (hV₀ : V₀.IsRational) (hVinf : Vinf.IsRational) :
    ∃ f : RatFunc k, f ≠ 0 ∧ ∀ V : Place k (RatFunc k),
      V.ord f = (if V = V₀ then 1 else 0) - (if V = Vinf then 1 else 0) := by
  classical
  let D : Divisor k (RatFunc k) := Finsupp.single V₀ 1 - Finsupp.single Vinf 1
  have hD : Divisor.degree D = 0 := by
    change Divisor.degree (Finsupp.single V₀ 1 - Finsupp.single Vinf 1) = 0
    rw [map_sub, Divisor.degree_single, Divisor.degree_single,
      (Place.isRational_iff_deg_eq_one V₀).mp hV₀,
      (Place.isRational_iff_deg_eq_one Vinf).mp hVinf, sub_self]
  obtain ⟨f, hf, hord⟩ := RationalFunctionField.isPrincipal_of_degree_eq_zero D hD
  refine ⟨f, hf, fun V => ?_⟩
  rw [← hord V]
  simp only [D, Finsupp.sub_apply, Finsupp.single_apply, eq_comm]

theorem ratFunc_exists_transcendental_function_rationalPlace_pair
    {k : Type*} [Field k]
    (V₀ Vinf : Place k (RatFunc k))
    (hV₀ : V₀.IsRational) (hVinf : Vinf.IsRational) (hne : V₀ ≠ Vinf) :
    ∃ f : RatFunc k, f ≠ 0 ∧ Transcendental k f ∧ ∀ V : Place k (RatFunc k),
      V.ord f = (if V = V₀ then 1 else 0) - (if V = Vinf then 1 else 0) := by
  classical
  obtain ⟨f, hf, hord⟩ := ratFunc_exists_function_rationalPlace_pair V₀ Vinf hV₀ hVinf
  have hpole : Vinf.ord f = -1 := by
    rw [hord, ite_eq_right hne.symm, ite_eq_left rfl]
    norm_num
  exact ⟨f, hf, Vinf.transcendental_of_ord_ne_zero (by omega), hord⟩

end AnabelianGeometry.KummerTheory
