/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.FunctionFields.Rational.RatFuncCoordinateFromAdjoin
import Nyll.AlgebraicCurves.Divisors.Degree.DegreeEqFinrankAdjoinEqMaxNegOrd
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.FiniteDimensionalLSpaceZero
import Nyll.AlgebraicCurves.FunctionFields.Rational.InstIsCurveOverRatFunc
import Nyll.AlgebraicCurves.FunctionFields.Extensions.CurveFiniteDimensionalAdjoinSimple
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.AlgebraicCurves.Places.Orders.TranscendentalOrdNeZero

/-! # The same simple-pole pair function is a rational-function coordinate

All finiteness hypotheses of the divisor degree formula are derived for k(t).
A rational simple pole has degree one. The resulting degree-one extension is
trivial, so the prescribed function itself, rather than a replacement, is the
image of X under a k-algebra automorphism.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open AlgebraicCurve

namespace AnabelianGeometry.KummerTheory

/-- Full pair orders force the extension k(t)/k(f) to have degree one. -/
theorem ratFunc_transcendental_and_finrank_eq_one_of_pair_orders
    {k : Type*} [Field k]
    (V₀ Vinf : Place k (RatFunc k)) (hVinf : Vinf.IsRational) (hne : V₀ ≠ Vinf)
    (f : RatFunc k)
    (hord : ∀ V : Place k (RatFunc k),
      V.ord f = (if V = V₀ then 1 else 0) - (if V = Vinf then 1 else 0)) :
    Transcendental k f ∧
      Module.finrank (IntermediateField.adjoin k {f}) (RatFunc k) = 1 := by
  classical
  have hpole : Vinf.ord f = -1 := by
    rw [hord, ite_eq_right hne.symm, ite_eq_left rfl]
    norm_num
  have htrans : Transcendental k f :=
    Vinf.transcendental_of_ord_ne_zero (by omega)
  let : IsCurveOver k (RatFunc k) := AlgebraicCurve.instIsCurveOverRatFunc k
  let : Nonempty (Place k (RatFunc k)) := ⟨Vinf⟩
  let : Algebra.EssFiniteType (Polynomial k) (RatFunc k) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial k))
  let : Algebra.EssFiniteType k (RatFunc k) :=
    Algebra.EssFiniteType.comp k (Polynomial k) (RatFunc k)
  let : FiniteDimensional k (LSpace (0 : Divisor k (RatFunc k))) :=
    finiteDimensional_lSpace_zero k (RatFunc k)
  let : FiniteDimensional (IntermediateField.adjoin k {f}) (RatFunc k) :=
    IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType htrans
  let D : Divisor k (RatFunc k) := Finsupp.single Vinf 1
  have hD : ∀ V : Place k (RatFunc k), D V = max 0 (-V.ord f) := by
    intro V
    change (Finsupp.single Vinf (1 : ℤ)) V = max 0 (-V.ord f)
    by_cases hvi : V = Vinf
    · subst V
      rw [Finsupp.single_eq_same, hpole]
      norm_num
    · rw [Finsupp.single_eq_of_ne hvi, hord, ite_eq_right hvi]
      split_ifs <;> norm_num
  have hdeg : Divisor.degree D = 1 := by
    change Divisor.degree (Finsupp.single Vinf (1 : ℤ)) = 1
    rw [Divisor.degree_single, (Place.isRational_iff_deg_eq_one Vinf).mp hVinf]
    norm_num
  have hdegree := Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord f htrans D hD
  rw [hdeg] at hdegree
  refine ⟨htrans, ?_⟩
  exact_mod_cast hdegree.symm

/-- The already chosen pair function is the actual image of X under an automorphism. -/
theorem ratFunc_exists_algEquiv_apply_X_of_pair_orders
    {k : Type*} [Field k]
    (V₀ Vinf : Place k (RatFunc k)) (hVinf : Vinf.IsRational) (hne : V₀ ≠ Vinf)
    (f : RatFunc k)
    (hord : ∀ V : Place k (RatFunc k),
      V.ord f = (if V = V₀ then 1 else 0) - (if V = Vinf then 1 else 0)) :
    ∃ e : RatFunc k ≃ₐ[k] RatFunc k, e RatFunc.X = f := by
  obtain ⟨htrans, hdegree⟩ :=
    ratFunc_transcendental_and_finrank_eq_one_of_pair_orders V₀ Vinf hVinf hne f hord
  exact ratFunc_exists_algEquiv_apply_X_of_finrank_eq_one f htrans hdegree

end AnabelianGeometry.KummerTheory
