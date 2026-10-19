/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.FunctionFields.Rational.RatFuncPairEvaluation
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationPairCoordinate

/-! # The same pair coordinate at the original chosen arithmetic cusp places

The place choice is literally the one used by the chosen arithmetic
normalization decomposition and its root specialization. The full geometric
orders of the unchanged arithmetic function give the zero, pole, and all third
values. Its coordinate is normalized by the actual value at one fixed third
cusp; all other regular cusp values are the corresponding ratios.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open AlgebraicGeometry AlgebraicCurve
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AlgebraicGeometry.ProjSpace

open AnabelianGeometry.KummerTheory

/-- The actual pair function, read at the SAME arithmetic places used for
normalization-prime specialization, defines the normalized coordinate. -/
theorem rationalConfiguration_pairFunction_normalized_at_thirdChosenPlace
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
    [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]
    (s : Finset (Projectivization k (k × k)))
    (a b c : s) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (V₀ Vinf : (projectiveLineRatFuncModel k).openBoundaryPlaces
      (rationalConfigurationOpen s).ι)
    (f : RatFunc k) (hf : f ≠ 0)
    (harith : ∀ V : Place k (RatFunc k),
      V.ord f = (if V = V₀.val then 1 else 0) - (if V = Vinf.val then 1 else 0))
    (hgeom : ∀ W : Place κ (RatFunc κ),
      W.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
        (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
        (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0)) :
    let V : s → Place k (RatFunc k) := fun x =>
      (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s
        (rationalConfigurationBoundaryPlace k κ s x)).choose
    (V a).evalAt f = 0 ∧ (V b).ord f = -1 ∧
    (V c).ord f = 0 ∧ (V c).evalAt f ≠ 0 ∧
    ∃ e : RatFunc k ≃ₐ[k] RatFunc k,
      e RatFunc.X = f / algebraMap k (RatFunc k) ((V c).evalAt f) ∧
      (V a).evalAt (e RatFunc.X) = 0 ∧ (V c).evalAt (e RatFunc.X) = 1 ∧
      ∀ d : s, d ≠ b →
        (V d).evalAt (e RatFunc.X) = (V d).evalAt f / (V c).evalAt f := by
  intro V
  have hV (x : s) : (V x).IsRational :=
    (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s
      (rationalConfigurationBoundaryPlace k κ s x)).choose_spec.1
  have horders (x : s) :
      (V x).ord f = (if x = a then (1 : ℤ) else 0) -
        (if x = b then (1 : ℤ) else 0) := by
    have hx := (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s
      (rationalConfigurationBoundaryPlace k κ s x)).choose_spec.2 f
    have hlabels (y : s) :
        (rationalConfigurationBoundaryPlace k κ s x).val =
          (rationalConfigurationBoundaryPlace k κ s y).val ↔ x = y := by
      constructor
      · intro h
        apply (rationalConfigurationBoundaryPlaceEquiv k κ s).injective
        exact Subtype.ext h
      · rintro rfl
        rfl
    simpa only [hlabels a, hlabels b] using hx.symm.trans (hgeom _)
  have ha : (V a).ord f = 1 := by
    rw [horders, ite_eq_left rfl, ite_eq_right hab, sub_zero]
  have hb : (V b).ord f = -1 := by
    rw [horders, ite_eq_right hab.symm, ite_eq_left rfl, zero_sub]
  have hc : (V c).ord f = 0 := by
    rw [horders, ite_eq_right hca, ite_eq_right hcb, sub_self]
  have ha0 : (V a).evalAt f = 0 :=
    ratFunc_evalAt_eq_zero_of_ord_pos (V a) f hf (by omega)
  have hc0 : (V c).evalAt f ≠ 0 := (V c).evalAt_ne_zero (hV c) hf hc
  obtain ⟨e₀, he₀⟩ := rationalConfiguration_pairFunction_exists_coordinate
    k κ s a b hab V₀ Vinf f harith hgeom
  obtain ⟨e, he⟩ := ratFunc_exists_normalized_coordinate e₀ f he₀ ((V c).evalAt f) hc0
  refine ⟨ha0, hb, hc, hc0, e, he, ?_, ?_, ?_⟩
  · rw [he, ratFunc_evalAt_div_constant (V a) (hV a) f hf (by omega), ha0, zero_div]
  · rw [he, ratFunc_evalAt_div_constant (V c) (hV c) f hf hc.ge, div_self hc0]
  · intro d hdb
    rw [he]
    apply ratFunc_evalAt_div_constant (V d) (hV d) f hf ?_ ((V c).evalAt f)
    rw [horders, ite_eq_right hdb, sub_zero]
    split_ifs <;> omega

end AlgebraicGeometry.ProjSpace
