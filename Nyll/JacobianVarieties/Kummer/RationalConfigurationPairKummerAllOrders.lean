/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.RationalConfigurationArithmeticPairKummerUnits

/-! # Keeping all orders of the same arithmetic pair function -/
noncomputable section
attribute [local instance] Classical.propDecidable
open AlgebraicGeometry AlgebraicCurve
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AlgebraicGeometry.ProjSpace
variable (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
  [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]

/-- The same selected function, both full divisors, and both actual Kummer units
are retained before passing to any exponent. -/
theorem rationalConfiguration_exists_pair_openKummerUnits_with_all_orders
    (s : Finset (Projectivization k (k × k))) (a b : s) :
    ∃ V₀ Vinf : (projectiveLineRatFuncModel k).openBoundaryPlaces
        (rationalConfigurationOpen s).ι,
    ∃ f : RatFunc k, f ≠ 0 ∧
      (∀ V : Place k (RatFunc k),
        V.ord f = (if V = V₀.val then 1 else 0) -
          (if V = Vinf.val then 1 else 0)) ∧
      (∀ W : Place κ (RatFunc κ),
        W.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
          (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
          (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0)) ∧
      ∀ n : ℕ+,
      ∃ u : Pic0.openKummerUnits k (RatFunc k)
          ((projectiveLineRatFuncModel k).openBoundaryPlaces
            (rationalConfigurationOpen s).ι) n,
      ∃ w : Pic0.openKummerUnits κ (RatFunc κ)
          ((projectiveLineRatFuncModel κ).openBoundaryPlaces
            (rationalConfigurationBaseChangeChart k κ s)) n,
        (u.val : RatFunc k) = f ∧
        (w.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) f ∧
        ∀ x : s,
          Multiplicative.toAdd
            (Pic0.openKummerResidue
              ((projectiveLineRatFuncModel κ).openBoundaryPlaces
                (rationalConfigurationBaseChangeChart k κ s)) n w)
            (rationalConfigurationBoundaryPlace k κ s x) =
              (if x = a then 1 else 0) - (if x = b then 1 else 0) := by
  obtain ⟨V₀, Vinf, f, hf, harith, hgeom⟩ :=
    rationalConfiguration_exists_pair_function_with_arithmetic_boundary k κ s a b
  refine ⟨V₀, Vinf, f, hf, harith, hgeom, fun n => ?_⟩
  let u : (RatFunc k)ˣ := Units.mk0 f hf
  let w : (RatFunc κ)ˣ := Units.mk0
    (algebraMap (RatFunc k) (RatFunc κ) f) ((map_ne_zero _).mpr hf)
  have hu : u ∈ Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces
        (rationalConfigurationOpen s).ι) n := by
    intro V hV
    have ha : V ≠ V₀.val := by
      intro h
      exact hV (h.symm ▸ V₀.property)
    have hb : V ≠ Vinf.val := by
      intro h
      exact hV (h.symm ▸ Vinf.property)
    change (n : ℤ) ∣ V.ord f
    rw [harith, ite_eq_right ha, ite_eq_right hb, sub_self]
    exact dvd_zero _
  have hw : w ∈ Pic0.openKummerUnits κ (RatFunc κ)
      ((projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ s)) n := by
    intro W hW
    have ha : W ≠ (rationalConfigurationBoundaryPlace k κ s a).val := by
      intro h
      exact hW (h.symm ▸ (rationalConfigurationBoundaryPlace k κ s a).property)
    have hb : W ≠ (rationalConfigurationBoundaryPlace k κ s b).val := by
      intro h
      exact hW (h.symm ▸ (rationalConfigurationBoundaryPlace k κ s b).property)
    change (n : ℤ) ∣ W.ord (algebraMap (RatFunc k) (RatFunc κ) f)
    rw [hgeom, ite_eq_right ha, ite_eq_right hb, sub_self]
    exact dvd_zero _
  refine ⟨⟨u, hu⟩, ⟨w, hw⟩, rfl, rfl, fun x => ?_⟩
  change (((rationalConfigurationBoundaryPlace k κ s x).val.ord
    (algebraMap (RatFunc k) (RatFunc κ) f)) : ZMod (n : ℕ)) = _
  have hlabels (y : s) :
      (rationalConfigurationBoundaryPlace k κ s x).val =
        (rationalConfigurationBoundaryPlace k κ s y).val ↔ x = y := by
    constructor
    · intro h
      apply (rationalConfigurationBoundaryPlaceEquiv k κ s).injective
      exact Subtype.ext h
    · rintro rfl
      rfl
  rw [hgeom, hlabels a, hlabels b]
  split_ifs <;> norm_num

end AlgebraicGeometry.ProjSpace
