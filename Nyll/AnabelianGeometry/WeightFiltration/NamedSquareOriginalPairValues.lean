/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationPairCrossRatio
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationFiniteExtensionCoordinate
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationFiniteExtensionValues
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationSquareBoundaryLabels
import Nyll.AlgebraicCurves.Places.Evaluation.RationalPlaceValues

/-! # Named Square Original Pair Values -/

noncomputable section
open scoped Polynomial RatFunc
open AlgebraicGeometry AlgebraicGeometry.ProjSpace AlgebraicCurve
open AnabelianGeometry.ProjectiveLine AnabelianGeometry.KummerTheory
attribute [local instance] Classical.propDecidable
  MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AnabelianGeometry.WeightFiltration

theorem namedSquare_pair_actual_values
    (k E : Type) [Field k] [Field E] [Algebra k E]
    (s : Finset (Projectivization k (k × k)))
    (a b c₀ : s) (hab : a ≠ b) (h₀b : c₀ ≠ b)
    (f : RatFunc E) (hf : f ≠ 0)
    (hord : ∀ W : Place E (RatFunc E), W.ord f =
      (if W = (rationalConfigurationBoundaryPlace k E s a).val then 1 else 0) -
      (if W = (rationalConfigurationBoundaryPlace k E s b).val then 1 else 0)) :
    let v : s → E := fun x => (rationalConfigurationBoundaryPlace k E s x).val.evalAt f
    v a = 0 ∧
    (rationalConfigurationBoundaryPlace k E s b).val.ord f < 0 ∧
    (∀ x : s, x ≠ b → (rationalConfigurationBoundaryPlace k E s x).val.HasValue f (v x)) ∧
    ∀ c : s, c ≠ b → v c / v c₀ =
      algebraMap k E (crossRatio a.val b.val c₀.val c.val) := by
  intro v
  have hlabels (x y : s) :
      (rationalConfigurationBoundaryPlace k E s x).val =
        (rationalConfigurationBoundaryPlace k E s y).val ↔ x = y := by
    constructor
    · intro h
      exact (rationalConfigurationBoundaryPlaceEquiv k E s).injective (Subtype.ext h)
    · intro h
      exact congrArg (fun z : s => (rationalConfigurationBoundaryPlace k E s z).val) h
  have horders (x : s) : (rationalConfigurationBoundaryPlace k E s x).val.ord f =
      (if x = a then (1 : ℤ) else 0) - (if x = b then (1 : ℤ) else 0) := by
    simpa only [hlabels] using hord (rationalConfigurationBoundaryPlace k E s x).val
  have ha : (rationalConfigurationBoundaryPlace k E s a).val.ord f = 1 := by
    rw [horders, ite_eq_left rfl, ite_eq_right hab, sub_zero]
  have hb : (rationalConfigurationBoundaryPlace k E s b).val.ord f = -1 := by
    rw [horders, ite_eq_right hab.symm, ite_eq_left rfl, zero_sub]
  refine ⟨ratFunc_evalAt_eq_zero_of_ord_pos _ f hf (by rw [ha]; norm_num),
    by rw [hb]; norm_num, ?_, ?_⟩
  · intro x hxb
    have hrat : (rationalConfigurationBoundaryPlace k E s x).val.IsRational := by
      rw [rationalConfigurationBoundaryPlace_eq_projectiveRatFuncPlace]
      exact projectiveRatFuncPlace_isRational _
    apply Place.hasValue_evalAt_of_ord_nonneg _ hrat f hf
    rw [horders, ite_eq_right hxb, sub_zero]
    split_ifs <;> norm_num
  · intro c hcb
    have hpoint (x y : s) (hxy : x ≠ y) :
        rationalConfigurationProjectivePoint k E x.val ≠
          rationalConfigurationProjectivePoint k E y.val := by
      intro h
      exact hxy (Subtype.ext (rationalConfigurationProjectivePoint_injective k E h))
    calc
      v c / v c₀ =
          crossRatio (rationalConfigurationProjectivePoint k E a.val)
            (rationalConfigurationProjectivePoint k E b.val)
            (rationalConfigurationProjectivePoint k E c₀.val)
            (rationalConfigurationProjectivePoint k E c.val) := by
        change (rationalConfigurationBoundaryPlace k E s c).val.evalAt f /
          (rationalConfigurationBoundaryPlace k E s c₀).val.evalAt f = _
        rw [rationalConfigurationBoundaryPlace_eq_projectiveRatFuncPlace,
          rationalConfigurationBoundaryPlace_eq_projectiveRatFuncPlace]
        apply ratFunc_pair_evalAt_ratio_eq_crossRatio _ _ _ _
          (hpoint c₀ b h₀b) (hpoint c b hcb) f hf
        intro W
        simpa only [rationalConfigurationBoundaryPlace_eq_projectiveRatFuncPlace] using hord W
      _ = algebraMap k E (crossRatio a.val b.val c₀.val c.val) :=
        crossRatio_rationalConfigurationProjectivePoint k E a.val b.val c₀.val c.val

theorem namedSquare_original_pair_values_over_extension
    (k κ E : Type) [Field k] [Field κ] [Field E]
    [Algebra k κ] [Algebra k E]
    [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]
    [Algebra.IsAlgebraic k E] [Algebra.IsSeparable k E]
    (s : Finset (Projectivization k (k × k)))
    (a b c₀ : s) (hab : a ≠ b) (h₀b : c₀ ≠ b)
    (V₀ Vinf : Place k (RatFunc k)) (f : RatFunc k) (hf : f ≠ 0)
    (harith : ∀ V : Place k (RatFunc k), V.ord f =
      (if V = V₀ then 1 else 0) - (if V = Vinf then 1 else 0))
    (hgeom : ∀ W : Place κ (RatFunc κ),
      W.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
        (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
        (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0)) :
    let fE := algebraMap (RatFunc k) (RatFunc E) f
    let v : s → E := fun x => (rationalConfigurationBoundaryPlace k E s x).val.evalAt fE
    v a = 0 ∧
    (rationalConfigurationBoundaryPlace k E s b).val.ord fE < 0 ∧
    (∀ x : s, x ≠ b →
      (rationalConfigurationBoundaryPlace k E s x).val.HasValue fE (v x)) ∧
    ∀ c : s, c ≠ b → v c / v c₀ =
      algebraMap k E (crossRatio a.val b.val c₀.val c.val) := by
  intro fE v
  obtain ⟨horders, _hcoordinate⟩ :=
    rationalConfiguration_pairFunction_finiteExtension_orders_coordinate
      k κ E s a b hab V₀ Vinf f harith hgeom
  have hfE : fE ≠ 0 := by
    simpa only [map_zero] using (algebraMap (RatFunc k) (RatFunc E)).injective.ne hf
  exact namedSquare_pair_actual_values k E s a b c₀ hab h₀b fE hfE horders

end AnabelianGeometry.WeightFiltration
