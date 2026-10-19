/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationPairFunction
import Nyll.JacobianVarieties.Kummer.OpenDivisorResidues
import Mathlib.Tactic.NormNum

/-! # Actual arithmetic pair functions and matching Kummer residues

A single function over k is chosen before the
exponent. Its scalar extension is an open Kummer unit for every exponent.
For any actual label equivalence, the two constructed functions have the
same residue vector. No function or residue agreement is an assumption.
-/

noncomputable section

attribute [local instance] Classical.propDecidable
open AlgebraicCurve
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AlgebraicGeometry.ProjSpace

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
  [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]

/-- One arithmetic function supplies all exponents and their actual residues. -/
theorem rationalConfiguration_exists_pair_openKummerUnits
    (s : Finset (Projectivization k (k × k))) (a b : s) :
    ∃ f : RatFunc k, f ≠ 0 ∧ ∀ n : ℕ+,
      ∃ w : Pic0.openKummerUnits κ (RatFunc κ)
          ((projectiveLineRatFuncModel κ).openBoundaryPlaces
            (rationalConfigurationBaseChangeChart k κ s)) n,
        (w.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) f ∧
        ∀ x : s,
          Multiplicative.toAdd
            (Pic0.openKummerResidue
              ((projectiveLineRatFuncModel κ).openBoundaryPlaces
                (rationalConfigurationBaseChangeChart k κ s)) n w)
            (rationalConfigurationBoundaryPlace k κ s x) =
              (if x = a then 1 else 0) - (if x = b then 1 else 0) := by
  classical
  obtain ⟨f, hf, hord⟩ := rationalConfiguration_exists_pair_function k κ s a b
  refine ⟨f, hf, fun n => ?_⟩
  let S := (projectiveLineRatFuncModel κ).openBoundaryPlaces
    (rationalConfigurationBaseChangeChart k κ s)
  let u : (RatFunc κ)ˣ := Units.mk0
    (algebraMap (RatFunc k) (RatFunc κ) f) ((map_ne_zero _).mpr hf)
  have hu : u ∈ Pic0.openKummerUnits κ (RatFunc κ) S n := by
    intro W hW
    have ha : W ≠ (rationalConfigurationBoundaryPlace k κ s a).val := by
      intro h
      exact hW (h.symm ▸ (rationalConfigurationBoundaryPlace k κ s a).property)
    have hb : W ≠ (rationalConfigurationBoundaryPlace k κ s b).val := by
      intro h
      exact hW (h.symm ▸ (rationalConfigurationBoundaryPlace k κ s b).property)
    change (n : ℤ) ∣ W.ord (algebraMap (RatFunc k) (RatFunc κ) f)
    rw [hord, ite_eq_right ha, ite_eq_right hb, sub_self]
    exact dvd_zero _
  refine ⟨⟨u, hu⟩, rfl, fun x => ?_⟩
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
  rw [hord, hlabels a, hlabels b]
  split_ifs <;> norm_num

/-- The label equivalence, including the one reconstructed from inertia,
produces matching residues of two actual arithmetic pair functions. -/
theorem rationalConfigurations_exists_pair_matching_openKummerResidues
    (s t : Finset (Projectivization k (k × k))) (e : s ≃ t) (a b : s) :
    ∃ f g : RatFunc k, f ≠ 0 ∧ g ≠ 0 ∧ ∀ n : ℕ+,
      ∃ ws : Pic0.openKummerUnits κ (RatFunc κ)
          ((projectiveLineRatFuncModel κ).openBoundaryPlaces
            (rationalConfigurationBaseChangeChart k κ s)) n,
      ∃ wt : Pic0.openKummerUnits κ (RatFunc κ)
          ((projectiveLineRatFuncModel κ).openBoundaryPlaces
            (rationalConfigurationBaseChangeChart k κ t)) n,
        (ws.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) f ∧
        (wt.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) g ∧
        ∀ x : s,
          Multiplicative.toAdd (Pic0.openKummerResidue _ n ws)
              (rationalConfigurationBoundaryPlace k κ s x) =
            Multiplicative.toAdd (Pic0.openKummerResidue _ n wt)
              (rationalConfigurationBoundaryPlace k κ t (e x)) := by
  classical
  obtain ⟨f, hf, hfs⟩ := rationalConfiguration_exists_pair_openKummerUnits k κ s a b
  obtain ⟨g, hg, hgt⟩ :=
    rationalConfiguration_exists_pair_openKummerUnits k κ t (e a) (e b)
  refine ⟨f, g, hf, hg, fun n => ?_⟩
  obtain ⟨ws, hws, hrs⟩ := hfs n
  obtain ⟨wt, hwt, hrt⟩ := hgt n
  refine ⟨ws, wt, hws, hwt, fun x => ?_⟩
  rw [hrs x, hrt (e x)]
  simp only [e.injective.eq_iff]

end AlgebraicGeometry.ProjSpace
