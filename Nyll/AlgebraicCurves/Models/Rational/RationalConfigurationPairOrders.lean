/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationBoundaryPlaceOrders

/-! # Ordinary orders of a rational pair function at a third labelled place -/
noncomputable section
attribute [local instance] Classical.propDecidable
open AlgebraicGeometry AlgebraicCurve
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AlgebraicGeometry.ProjSpace
variable (k κ : Type) [Field k] [Field κ] [Algebra k κ]

/-- A third labelled cusp has order zero for this same function. -/
theorem rationalConfiguration_pair_order_eq_zero_at_other_label
    (s : Finset (Projectivization k (k × k))) (a b c : s)
    (hac : c ≠ a) (hbc : c ≠ b) (f : RatFunc k)
    (hgeom : ∀ W : Place κ (RatFunc κ),
      W.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
        (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
        (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0)) :
    (rationalConfigurationBoundaryPlace k κ s c).val.ord
      (algebraMap (RatFunc k) (RatFunc κ) f) = 0 := by
  have hca : (rationalConfigurationBoundaryPlace k κ s c).val ≠
      (rationalConfigurationBoundaryPlace k κ s a).val := by
    intro h
    apply hac
    exact (rationalConfigurationBoundaryPlaceEquiv k κ s).injective (Subtype.ext h)
  have hcb : (rationalConfigurationBoundaryPlace k κ s c).val ≠
      (rationalConfigurationBoundaryPlace k κ s b).val := by
    intro h
    apply hbc
    exact (rationalConfigurationBoundaryPlaceEquiv k κ s).injective (Subtype.ext h)
  rw [hgeom, ite_eq_right hca, ite_eq_right hcb, sub_self]

variable [IsAlgClosed κ] [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]

/-- The same third cusp supplies an actual rational arithmetic place where
this function has order zero, with its full coefficient-extension order comparison. -/
theorem rationalConfiguration_pair_exists_arithmetic_order_eq_zero_at_other_label
    (s : Finset (Projectivization k (k × k))) (a b c : s)
    (hac : c ≠ a) (hbc : c ≠ b) (f : RatFunc k)
    (hgeom : ∀ W : Place κ (RatFunc κ),
      W.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
        (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
        (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0)) :
    ∃ V : Place k (RatFunc k), V.IsRational ∧
      (∀ z : RatFunc k,
        (rationalConfigurationBoundaryPlace k κ s c).val.ord
          (algebraMap (RatFunc k) (RatFunc κ) z) = V.ord z) ∧ V.ord f = 0 := by
  obtain ⟨V, hV, hord⟩ := rationalConfigurationBoundaryPlace_exists_rationalPlace k κ s c
  refine ⟨V, hV, hord, ?_⟩
  rw [← hord f]
  exact rationalConfiguration_pair_order_eq_zero_at_other_label k κ s a b c hac hbc f hgeom

end AlgebraicGeometry.ProjSpace
