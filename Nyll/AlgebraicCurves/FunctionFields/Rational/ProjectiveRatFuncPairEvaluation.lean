/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.FunctionFields.Rational.RatFuncPairEvaluation
import Nyll.SchemeTheory.ProjectiveSpace.Normalization
import Nyll.AlgebraicCurves.Places.Rational.Classification
import Nyll.AlgebraicCurves.Places.Rational.InfinityArithmetic
import Nyll.AlgebraicCurves.Places.Rational.RatFuncOrdXSubC
import Nyll.AlgebraicCurves.Places.Rational.RatFuncEvalAtPlaceInftyEq
import Nyll.AlgebraicCurves.Places.Rational.RatFuncEvalAtPlaceOfPointAlgebraMap
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation

/-! # Explicit projective pair functions and their actual place evaluations

The standard rational-function place attached to a homogeneous point includes
infinity. The bracket quotient has the corresponding simple zero and pole, and
its evaluation is the homogeneous bracket quotient. Comparison of all orders
then reads the normalized values of any given pair function as cross ratios.
No replacement of that given function occurs in the conclusion.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open AlgebraicCurve
open scoped Polynomial RatFunc

namespace AnabelianGeometry.ProjectiveLine

open AnabelianGeometry.KummerTheory AlgebraicCurve.RationalFunctionField

variable {k : Type*} [Field k]

/-- The standard rational-function place of the actual homogeneous coordinates. -/
def projectiveRatFuncPlace (p : Projectivization k (k × k)) : Place k (RatFunc k) :=
  if p.rep.2 = 0 then placeInfty k else placeOfPoint k (p.rep.1 / p.rep.2)

/-- The affine linear form associated to one homogeneous point. -/
def pairLinearPolynomial (v : k × k) : Polynomial k :=
  Polynomial.C v.2 * Polynomial.X - Polynomial.C v.1

/-- The same linear form viewed in the rational function field. -/
def pairLinearRatFunc (v : k × k) : RatFunc k :=
  algebraMap (Polynomial k) (RatFunc k) (pairLinearPolynomial v)

/-- The unnormalized bracket quotient for the ordered pair. -/
def pairRatFunc (a b : Projectivization k (k × k)) : RatFunc k :=
  pairLinearRatFunc a.rep / pairLinearRatFunc b.rep

private theorem pairLinearPolynomial_ne_zero (v : k × k) (hv : v ≠ 0) :
    pairLinearPolynomial v ≠ 0 := by
  intro h
  have h₂ : v.2 = 0 := by
    simpa [pairLinearPolynomial] using congrArg (fun p : Polynomial k => p.coeff 1) h
  have h₁ : v.1 = 0 := by
    simpa [pairLinearPolynomial] using congrArg (fun p : Polynomial k => p.coeff 0) h
  exact hv (Prod.ext h₁ h₂)

theorem pairLinearRatFunc_ne_zero (v : k × k) (hv : v ≠ 0) :
    pairLinearRatFunc v ≠ 0 :=
  RatFunc.algebraMap_ne_zero (pairLinearPolynomial_ne_zero v hv)

private theorem pairLinearRatFunc_factor (v : k × k) (hv : v.2 ≠ 0) :
    pairLinearRatFunc v = RatFunc.C v.2 *
      algebraMap (Polynomial k) (RatFunc k) (Polynomial.X - Polynomial.C (v.1 / v.2)) := by
  have hcoef : v.2 * (v.1 / v.2) = v.1 := by field_simp
  have hp : pairLinearPolynomial v =
      Polynomial.C v.2 * (Polynomial.X - Polynomial.C (v.1 / v.2)) := by
    rw [pairLinearPolynomial, mul_sub, ← Polynomial.C_mul, hcoef]
  rw [pairLinearRatFunc, hp, map_mul, RatFunc.algebraMap_C]

theorem projectiveRatFuncPlace_injective :
    Function.Injective (projectiveRatFuncPlace (k := k)) := by
  intro p q h
  apply (bracket_rep_eq_zero_iff p q).mp
  by_cases hp : p.rep.2 = 0
  · by_cases hq : q.rep.2 = 0
    · simp only [bracket, hp, hq, mul_zero, zero_mul, sub_self]
    · have heq : placeInfty k = placeOfPoint k (q.rep.1 / q.rep.2) := by
        simpa only [projectiveRatFuncPlace, ite_eq_left hp, ite_eq_right hq] using h
      exact ((placeOfPoint_ne_placeInfty k _ ) heq.symm).elim
  · by_cases hq : q.rep.2 = 0
    · have heq : placeOfPoint k (p.rep.1 / p.rep.2) = placeInfty k := by
        simpa only [projectiveRatFuncPlace, ite_eq_right hp, ite_eq_left hq] using h
      exact ((placeOfPoint_ne_placeInfty k _) heq).elim
    · have heq : p.rep.1 / p.rep.2 = q.rep.1 / q.rep.2 :=
        placeOfPoint_injective k (by
          simpa only [projectiveRatFuncPlace, ite_eq_right hp, ite_eq_right hq] using h)
      have hcross := (div_eq_div_iff hp hq).mp heq
      unfold bracket
      rw [hcross, mul_comm q.rep.1 p.rep.2, sub_self]

theorem projectiveRatFuncPlace_isRational (p : Projectivization k (k × k)) :
    (projectiveRatFuncPlace p).IsRational := by
  apply (Place.isRational_iff_deg_eq_one _).mpr
  by_cases hp : p.rep.2 = 0
  · rw [projectiveRatFuncPlace, ite_eq_left hp]
    exact deg_placeInfty k
  · rw [projectiveRatFuncPlace, ite_eq_right hp]
    exact deg_placeOfPoint k _

/-- All orders of the linear form, including its cancellation at infinity. -/
theorem pairLinearRatFunc_orders (p : Projectivization k (k × k))
    (V : Place k (RatFunc k)) :
    V.ord (pairLinearRatFunc p.rep) =
      (if V = projectiveRatFuncPlace p then 1 else 0) -
        (if V = placeInfty k then 1 else 0) := by
  by_cases hp : p.rep.2 = 0
  · have hL : pairLinearRatFunc p.rep = algebraMap k (RatFunc k) (-p.rep.1) := by
      simp only [pairLinearRatFunc, pairLinearPolynomial, hp, map_zero, zero_mul,
        zero_sub, map_neg, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
    rw [hL, V.ord_algebraMap]
    simp only [projectiveRatFuncPlace, ite_eq_left hp, sub_self]
  · rw [show projectiveRatFuncPlace p = placeOfPoint k (p.rep.1 / p.rep.2) from
      ite_eq_right hp]
    rw [pairLinearRatFunc_factor p.rep hp,
      V.ord_mul (by simpa only [← RatFunc.algebraMap_eq_C] using
        (map_ne_zero (algebraMap k (RatFunc k))).mpr hp)
        (RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero _)),
      ← RatFunc.algebraMap_eq_C, V.ord_algebraMap, zero_add, ord_X_sub_C]
    simp only [Finsupp.add_apply, Finsupp.single_apply, eq_comm]
    split_ifs <;> norm_num

/-- The explicit bracket quotient has the complete required pair divisor. -/
theorem pairRatFunc_orders (a b : Projectivization k (k × k))
    (V : Place k (RatFunc k)) :
    V.ord (pairRatFunc a b) =
      (if V = projectiveRatFuncPlace a then 1 else 0) -
        (if V = projectiveRatFuncPlace b then 1 else 0) := by
  rw [pairRatFunc, div_eq_mul_inv,
    V.ord_mul (pairLinearRatFunc_ne_zero a.rep a.rep_nonzero)
      (inv_ne_zero (pairLinearRatFunc_ne_zero b.rep b.rep_nonzero)),
    V.ord_inv, pairLinearRatFunc_orders, pairLinearRatFunc_orders]
  ring

private theorem pairLinearRatFunc_intDegree (v : k × k) (hv : v.2 ≠ 0) :
    (pairLinearRatFunc v).intDegree = 1 := by
  rw [pairLinearRatFunc_factor v hv,
    RatFunc.intDegree_mul (by simpa only [← RatFunc.algebraMap_eq_C] using
      (map_ne_zero (algebraMap k (RatFunc k))).mpr hv)
      (RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero _)),
    RatFunc.intDegree_C, RatFunc.intDegree_polynomial, Polynomial.natDegree_X_sub_C];
    norm_num

private theorem pairRatFunc_evalAt_infty (a b : Projectivization k (k × k))
    (hb : b.rep.2 ≠ 0) :
    (placeInfty k).evalAt (pairRatFunc a b) = a.rep.2 / b.rep.2 := by
  apply evalAt_placeInfty_eq k
  let c : k := (a.rep.2 * b.rep.1 - a.rep.1 * b.rep.2) / b.rep.2
  have hden : pairLinearRatFunc b.rep ≠ 0 :=
    pairLinearRatFunc_ne_zero b.rep b.rep_nonzero
  have hdiff : pairRatFunc a b - algebraMap k (RatFunc k) (a.rep.2 / b.rep.2) =
      RatFunc.C c / pairLinearRatFunc b.rep := by
    apply (eq_div_iff hden).mpr
    rw [sub_mul, pairRatFunc, div_mul_cancel₀ _ hden]
    dsimp only [pairLinearRatFunc, pairLinearPolynomial, c]
    simp only [map_sub, map_mul, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
      RatFunc.algebraMap_eq_C, map_div₀]
    have hb' : (RatFunc.C b.rep.2 : RatFunc k) ≠ 0 :=
      (map_ne_zero RatFunc.C).mpr hb
    field_simp
    ring
  rw [hdiff]
  by_cases hc : c = 0
  · exact Or.inl (by rw [hc, map_zero, zero_div])
  · apply Or.inr
    rw [RatFunc.intDegree_div ((map_ne_zero RatFunc.C).mpr hc) hden,
      RatFunc.intDegree_C, pairLinearRatFunc_intDegree b.rep hb]
    norm_num

/-- Evaluation of the explicit pair function at every point away from its pole. -/
theorem pairRatFunc_evalAt (a b d : Projectivization k (k × k)) (hdb : d ≠ b) :
    (projectiveRatFuncPlace d).evalAt (pairRatFunc a b) =
      bracket d.rep a.rep / bracket d.rep b.rep := by
  have hdb' : bracket d.rep b.rep ≠ 0 :=
    fun h => hdb ((bracket_rep_eq_zero_iff d b).mp h)
  by_cases hd : d.rep.2 = 0
  · have hd₁ : d.rep.1 ≠ 0 := by
      intro h
      exact d.rep_nonzero (Prod.ext h hd)
    have hb : b.rep.2 ≠ 0 := by
      intro h
      exact hdb' (by simp only [bracket, hd, h, mul_zero, zero_mul, sub_self])
    rw [projectiveRatFuncPlace, ite_eq_left hd, pairRatFunc_evalAt_infty a b hb]
    simp only [bracket, hd, zero_mul, sub_zero]
    exact (mul_div_mul_left _ _ hd₁).symm
  · let V := projectiveRatFuncPlace d
    have hV : V.IsRational := projectiveRatFuncPlace_isRational d
    have hVeq : V = placeOfPoint k (d.rep.1 / d.rep.2) := by
      exact ite_eq_right hd
    have hVinf : V ≠ placeInfty k := by
      rw [hVeq]
      exact placeOfPoint_ne_placeInfty k _
    have hVb : V ≠ projectiveRatFuncPlace b := projectiveRatFuncPlace_injective.ne hdb
    have hdenord : V.ord (pairLinearRatFunc b.rep) = 0 := by
      rw [pairLinearRatFunc_orders, ite_eq_right hVb, ite_eq_right hVinf, sub_self]
    have hden : pairLinearRatFunc b.rep ≠ 0 :=
      pairLinearRatFunc_ne_zero b.rep b.rep_nonzero
    have hnum : pairLinearRatFunc a.rep ∈ V.toValuationSubring := by
      rw [hVeq]
      change algebraMap (Polynomial k) (RatFunc k) (pairLinearPolynomial a.rep) ∈
        (placeOfPoint k (d.rep.1 / d.rep.2)).toValuationSubring
      exact algebraMap_mem_ofHeightOneSpectrum k _ _
    change V.evalAt (pairLinearRatFunc a.rep / pairLinearRatFunc b.rep) = _
    rw [div_eq_mul_inv, V.evalAt_mul hV hnum
      (V.mem_of_ord_nonneg (inv_ne_zero hden) (by rw [V.ord_inv, hdenord]; omega)),
      V.evalAt_inv hV hden hdenord]
    rw [hVeq]
    change (placeOfPoint k (d.rep.1 / d.rep.2)).evalAt
        (algebraMap (Polynomial k) (RatFunc k) (pairLinearPolynomial a.rep)) *
      ((placeOfPoint k (d.rep.1 / d.rep.2)).evalAt
        (algebraMap (Polynomial k) (RatFunc k) (pairLinearPolynomial b.rep)))⁻¹ = _
    rw [evalAt_placeOfPoint_algebraMap, evalAt_placeOfPoint_algebraMap]
    simp only [pairLinearPolynomial, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, ← div_eq_mul_inv]
    have hlin (v : k × k) : v.2 * (d.rep.1 / d.rep.2) - v.1 =
        bracket d.rep v / d.rep.2 := by
      unfold bracket
      field_simp
    rw [hlin a.rep, hlin b.rep]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    rw [show (bracket d.rep a.rep * d.rep.2⁻¹) *
        (d.rep.2 * (bracket d.rep b.rep)⁻¹) =
        bracket d.rep a.rep * (d.rep.2⁻¹ * d.rep.2) * (bracket d.rep b.rep)⁻¹ by ring,
      inv_mul_cancel₀ hd, mul_one]

/-- The normalized evaluations of the SAME function are the projective cross ratios. -/
theorem ratFunc_pair_evalAt_ratio_eq_crossRatio
    (a b c d : Projectivization k (k × k))
    (hcb : c ≠ b) (hdb : d ≠ b)
    (f : RatFunc k) (hf : f ≠ 0)
    (hord : ∀ V : Place k (RatFunc k),
      V.ord f = (if V = projectiveRatFuncPlace a then 1 else 0) -
        (if V = projectiveRatFuncPlace b then 1 else 0)) :
    (projectiveRatFuncPlace d).evalAt f / (projectiveRatFuncPlace c).evalAt f =
      crossRatio a b c d := by
  have hreg (p : Projectivization k (k × k)) (hp : p ≠ b) :
      0 ≤ (projectiveRatFuncPlace p).ord (pairRatFunc a b) := by
    rw [pairRatFunc_orders, ite_eq_right (projectiveRatFuncPlace_injective.ne hp), sub_zero]
    split_ifs <;> omega
  rw [ratFunc_evalAt_ratio_eq_of_same_orders f (pairRatFunc a b) hf
    (div_ne_zero (pairLinearRatFunc_ne_zero a.rep a.rep_nonzero)
      (pairLinearRatFunc_ne_zero b.rep b.rep_nonzero))
    (fun V => (hord V).trans (pairRatFunc_orders a b V).symm)
    (projectiveRatFuncPlace c) (projectiveRatFuncPlace d)
    (projectiveRatFuncPlace_isRational c) (projectiveRatFuncPlace_isRational d)
    (hreg c hcb) (hreg d hdb), pairRatFunc_evalAt a b d hdb, pairRatFunc_evalAt a b c hcb]
  change (_ / _) / (_ / _) = (_ * _) / (_ * _)
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end AnabelianGeometry.ProjectiveLine
