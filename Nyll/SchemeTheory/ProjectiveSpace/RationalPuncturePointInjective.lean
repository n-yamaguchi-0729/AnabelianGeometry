/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.ProjectiveSpace.RationalPunctureCoordinateChange
import Nyll.SchemeTheory.ProjectiveSpace.Normalization
import Nyll.SchemeTheory.ProjectiveSpace.CrossRatioSeparation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # Injectivity of the actual rational projective point map -/

noncomputable section
open AlgebraicGeometry MvPolynomial
open AnabelianGeometry.ProjectiveLine

namespace AlgebraicGeometry.ProjSpace

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "P₂" => MvPolynomial (Fin 2) K
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 2) K

/-- Two rational puncture equations with a common projective zero have
proportional homogeneous coordinates. No rational-point classification is used. -/
theorem bracket_eq_zero_of_common_puncture_zero
    (v w : K × K) (hv : v ≠ 0) (p : ProjectiveSpectrum 𝒜)
    (hpv : punctureForm v ∈ p.asHomogeneousIdeal)
    (hpw : punctureForm w ∈ p.asHomogeneousIdeal) :
    bracket v w = 0 := by
  by_contra hdet
  obtain ⟨j, hj⟩ := exists_nonzero_puncture_coordinate v hv
  let I : Ideal P₂ := p.asHomogeneousIdeal.toIdeal
  have hprime : I.IsPrime := p.isPrime
  have hpv' : punctureForm v ∈ I := hpv
  have hpw' : punctureForm w ∈ I := hpw
  have hprod : C (bracket v w) * X j ∈ I := by
    fin_cases j
    · change C (bracket v w) * X (0 : Fin 2) ∈ I
      have heq : C v.1 * punctureForm w - C w.1 * punctureForm v =
          C (bracket v w) * X 0 := by
        simp only [punctureForm, bracket, map_sub, map_mul]
        ring
      rw [← heq]
      exact I.sub_mem (I.mul_mem_left (C v.1) hpw')
        (I.mul_mem_left (C w.1) hpv')
    · change C (bracket v w) * X (1 : Fin 2) ∈ I
      have heq : C v.2 * punctureForm w - C w.2 * punctureForm v =
          C (bracket v w) * X 1 := by
        simp only [punctureForm, bracket, map_sub, map_mul]
        ring
      rw [← heq]
      exact I.sub_mem (I.mul_mem_left (C v.2) hpw')
        (I.mul_mem_left (C w.2) hpv')
  have hX : (X j : P₂) ∉ I := linearForm_zero_implies_chart v j hj p hpv
  have hC : C (bracket v w) ∈ I :=
    (hprime.mul_mem_iff_mem_or_mem.mp hprod).resolve_right hX
  have hmul := I.mul_mem_left (C (bracket v w)⁻¹) hC
  have hOne : (1 : P₂) ∈ I := by
    simpa only [← map_mul, inv_mul_cancel₀ hdet, map_one] using hmul
  exact hprime.ne_top (I.eq_top_iff_one.mpr hOne)

/-- Distinct projective labels determine distinct actual scheme points. -/
theorem projectiveRationalPoint_injective :
    Function.Injective (projectiveRationalPoint (K := K)) := by
  intro p q hpq
  apply (bracket_rep_eq_zero_iff p q).mp
  apply bracket_eq_zero_of_common_puncture_zero
    p.rep q.rep p.rep_nonzero (projectiveRationalPoint p)
  · exact punctureForm_mem_rationalPuncturePoint p.rep p.rep_nonzero
  · rw [hpq]
    exact punctureForm_mem_rationalPuncturePoint q.rep q.rep_nonzero

@[simp] theorem projectiveRationalPoint_eq_iff
    (p q : Projectivization K (K × K)) :
    projectiveRationalPoint p = projectiveRationalPoint q ↔ p = q :=
  projectiveRationalPoint_injective.eq_iff

/-- The constructed rational point identifies exactly the intended projective class. -/
theorem rationalPuncturePoint_eq_iff_mk_eq
    (v w : K × K) (hv : v ≠ 0) (hw : w ≠ 0) :
    rationalPuncturePoint v hv = rationalPuncturePoint w hw ↔
      Projectivization.mk K v hv = Projectivization.mk K w hw := by
  simpa only [projectiveRationalPoint_mk] using
    (projectiveRationalPoint_eq_iff
      (Projectivization.mk K v hv) (Projectivization.mk K w hw))

end AlgebraicGeometry.ProjSpace

namespace AnabelianGeometry.ProjectiveLine

universe u
variable {K : Type u} [Field K]

/-- The standard finite-point chart embeds the coefficient field in the projective line. -/
theorem affinePoint_injective : Function.Injective (affinePoint (K := K)) := by
  intro s t h
  unfold affinePoint at h
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
  have hc1 : c = 1 := by
    simpa only [Prod.smul_snd, smul_eq_mul, mul_one] using congrArg Prod.snd hc
  have hc0 := congrArg Prod.fst hc
  simpa only [Prod.smul_fst, smul_eq_mul, hc1, one_mul] using hc0.symm

end AnabelianGeometry.ProjectiveLine
