/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.FunctionFields.Rational.RatFuncPairFunctionCoordinate
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationBoundaryPlaceOrders

/-! # A coordinate for the already chosen configuration pair function

The retained arithmetic order formula need not separately carry rationality
or distinctness of its two arithmetic boundary witnesses. The geometric order
formula at the labelled pole, and the existing rational-place supplier for
that same label, recover both facts for the given function.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open AlgebraicGeometry AlgebraicCurve
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AlgebraicGeometry.ProjSpace

open AnabelianGeometry.KummerTheory

/-- No function is selected here: the two full order formulas for the existing f
supply its arithmetic rational pole and hence an automorphism sending X to f. -/
theorem rationalConfiguration_pairFunction_exists_coordinate
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
    [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]
    (s : Finset (Projectivization k (k × k))) (a b : s) (hab : a ≠ b)
    (V₀ Vinf : (projectiveLineRatFuncModel k).openBoundaryPlaces
      (rationalConfigurationOpen s).ι)
    (f : RatFunc k)
    (harith : ∀ V : Place k (RatFunc k),
      V.ord f = (if V = V₀.val then 1 else 0) - (if V = Vinf.val then 1 else 0))
    (hgeom : ∀ W : Place κ (RatFunc κ),
      W.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
        (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
        (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0)) :
    ∃ e : RatFunc k ≃ₐ[k] RatFunc k, e RatFunc.X = f := by
  classical
  obtain ⟨Vb, hVb, hordb⟩ :=
    rationalConfigurationBoundaryPlace_exists_rationalPlace k κ s b
  have hba : (rationalConfigurationBoundaryPlace k κ s b).val ≠
      (rationalConfigurationBoundaryPlace k κ s a).val := by
    intro h
    apply hab
    exact ((rationalConfigurationBoundaryPlaceEquiv k κ s).injective (Subtype.ext h)).symm
  have hpole : Vb.ord f = -1 := by
    rw [← hordb f, hgeom, ite_eq_right hba, ite_eq_left rfl]
    norm_num
  have hVbinf : Vb = Vinf.val := by
    by_contra hne
    have h := harith Vb
    rw [ite_eq_right hne, hpole] at h
    split_ifs at h <;> norm_num at h
  have hdistinct : V₀.val ≠ Vinf.val := by
    intro hne
    have h := harith Vb
    rw [hne, sub_self, hpole] at h
    norm_num at h
  have hVinf : Vinf.val.IsRational := hVbinf ▸ hVb
  exact ratFunc_exists_algEquiv_apply_X_of_pair_orders
    V₀.val Vinf.val hVinf hdistinct f harith

end AlgebraicGeometry.ProjSpace
