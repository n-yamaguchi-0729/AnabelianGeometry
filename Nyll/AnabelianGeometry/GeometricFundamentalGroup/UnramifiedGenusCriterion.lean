/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Extensions.FiniteSimpleExtensions
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.TwoMulGenusFFSubTwoEqSeparable
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveSeparatingTranscendental
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveTranscendentalPerfectField
import Nyll.AlgebraicCurves.Places.Ramification.FiniteRamification
import Mathlib.Algebra.BigOperators.Finprod

/-! # Detecting unramified covers from their genera

For a finite extension of curve function fields in characteristic zero,
equality in Riemann--Hurwitz is equivalent to every ramification index being
one. This is the numerical criterion underlying Tamagawa, *The Grothendieck
conjecture for affine curves* (1997), Proposition (3.7), p. 161:
https://doi.org/10.1023/A:1000114400142.

The results use the actual extension and its degree. A ramification formula,
a finite exceptional set, and values for the two genera are not inputs.
-/

noncomputable section

open AlgebraicCurve

namespace AnabelianGeometry.GeometricFundamentalGroup

variable {K F E : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  [Field F] [Field E] [Algebra K F] [Algebra K E] [Algebra F E]
  [IsScalarTower K F E] [FiniteDimensional F E]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]

omit [IsAlgClosed K] [CharZero K] [Algebra K F] [IsScalarTower K F E]
  [IsCurveOver K F] [Algebra.EssFiniteType K F] in
private theorem ramification_defect_nonneg (w : Place K E) :
    0 ≤ (w.ramificationIndex F : ℤ) - 1 := by
  have h := w.ramificationIndex_pos (F := F)
  omega

private theorem genus_formula_charZero :
    2 * (genusFF K E : ℤ) - 2 =
      (Module.finrank F E : ℤ) * (2 * (genusFF K F : ℤ) - 2) +
        ∑ᶠ w : Place K E, ((w.ramificationIndex F : ℤ) - 1) := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  obtain ⟨t, ht, hfinite, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  exact two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame ⟨t, ht, hfinite⟩
    (fun w => Nat.cast_ne_zero.mpr (w.ramificationIndex_pos (F := F)).ne')

/-- The degree gives the usual lower bound for the genus of a cover. -/
theorem degree_mul_two_genus_sub_two_le :
    (Module.finrank F E : ℤ) * (2 * (genusFF K F : ℤ) - 2) ≤
      2 * (genusFF K E : ℤ) - 2 := by
  rw [genus_formula_charZero (K := K) (F := F) (E := E)]
  exact le_add_of_nonneg_right (finsum_nonneg (ramification_defect_nonneg (K := K) (F := F)))

/-- A finite cover is unramified at every place exactly when its degree and
genera satisfy the unramified Riemann--Hurwitz equality. -/
theorem unramified_iff_genus_equality :
    (∀ w : Place K E, w.ramificationIndex F = 1) ↔
      2 * (genusFF K E : ℤ) - 2 =
        (Module.finrank F E : ℤ) * (2 * (genusFF K F : ℤ) - 2) := by
  have : IsCurveOver K E := by
    obtain ⟨t, ht, hfinite, _⟩ :=
      IsCurveOver.exists_separating_transcendental (K := K) (F := F)
    exact isCurveOver_of_transcendental_of_perfectField
      ((transcendental_algebraMap_iff (algebraMap F E).injective).mpr ht)
      (AlgebraicCurve.finiteDimensional_adjoin_algebraMap
        (L := K) (F' := E) t hfinite)
  have : HasPrincipalDivisors K E := IsCurveOver.hasPrincipalDivisors
  constructor
  · intro h
    have hzero : (∑ᶠ w : Place K E, ((w.ramificationIndex F : ℤ) - 1)) = 0 :=
      finsum_eq_zero_of_forall_eq_zero (fun w => by rw [h w, Nat.cast_one, sub_self])
    rw [genus_formula_charZero (K := K) (F := F) (E := E), hzero, add_zero]
  · intro h w
    have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
    have hfinite : Function.HasFiniteSupport
        (fun v : Place K E => (v.ramificationIndex F : ℤ) - 1) := by
      apply (finite_setOf_ramificationIndex_ne_one (K := K) (F := F) (F' := E)).subset
      intro v hv he
      apply hv
      change (v.ramificationIndex F : ℤ) - 1 = 0
      rw [he, Nat.cast_one, sub_self]
    have hsum := genus_formula_charZero (K := K) (F := F) (E := E)
    have hzero : (∑ᶠ v : Place K E, ((v.ramificationIndex F : ℤ) - 1)) = 0 := by
      rw [h] at hsum
      exact (add_eq_left.mp hsum.symm)
    by_contra hw
    have hpos : 0 < (w.ramificationIndex F : ℤ) - 1 := by
      have he := w.ramificationIndex_pos (F := F)
      omega
    have hpositive := finsum_pos (ramification_defect_nonneg (K := K) (F := F))
      ⟨w, hpos⟩ hfinite
    rw [hzero] at hpositive
    exact (lt_irrefl 0) hpositive

end AnabelianGeometry.GeometricFundamentalGroup
