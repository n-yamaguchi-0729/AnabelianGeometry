/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.PunctureForms
import Mathlib.Tactic.FinCases

/-! # A projective puncture zero lies in a nonvanishing coordinate chart -/

noncomputable section

namespace AlgebraicGeometry.ProjSpace

universe u

open MvPolynomial

variable {K : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "P₂" => MvPolynomial (Fin 2) K
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 2) K

/-- A zero of the puncture equation lies in every chart where its coordinate is nonzero. -/
theorem linearForm_zero_implies_chart
    (v : K × K) (j : Fin 2)
    (hvj : (![v.1, v.2] : Fin 2 → K) j ≠ 0)
    (p : ProjectiveSpectrum 𝒜) (hlinear : punctureForm v ∈ p.asHomogeneousIdeal) :
    X j ∉ p.asHomogeneousIdeal := by
  intro hj
  let I : Ideal P₂ := p.asHomogeneousIdeal.toIdeal
  have hlinear' : C v.2 * X 0 - C v.1 * X 1 ∈ I := hlinear
  have hj' : (X j : P₂) ∈ I := hj
  have hX : ∀ i : Fin 2, (X i : P₂) ∈ I := by
    fin_cases j
    · have hv0 : v.1 ≠ 0 := by simpa using hvj
      have hX0 : (X 0 : P₂) ∈ I := hj'
      have hscaled : C v.1 * X 1 ∈ I := by
        have h := I.sub_mem (I.mul_mem_left (C v.2) hX0) hlinear'
        simpa only [sub_sub_cancel] using h
      have hX1 : (X 1 : P₂) ∈ I := by
        have h := I.mul_mem_left (C (v.1)⁻¹) hscaled
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hv0, map_one, one_mul] at h
        exact h
      intro i
      fin_cases i
      · exact hX0
      · exact hX1
    · have hv1 : v.2 ≠ 0 := by simpa using hvj
      have hX1 : (X 1 : P₂) ∈ I := hj'
      have hscaled : C v.2 * X 0 ∈ I := by
        have h := I.add_mem hlinear' (I.mul_mem_left (C v.1) hX1)
        simpa only [sub_add_cancel] using h
      have hX0 : (X 0 : P₂) ∈ I := by
        have h := I.mul_mem_left (C (v.2)⁻¹) hscaled
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hv1, map_one, one_mul] at h
        exact h
      intro i
      fin_cases i
      · exact hX0
      · exact hX1
  have hspan : Ideal.span (Set.range (MvPolynomial.X : Fin 2 → P₂)) ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hX i
  apply p.not_irrelevant_le
  intro f hf
  exact hspan ((irrelevant_le_span_X K 1) hf)

end AlgebraicGeometry.ProjSpace
