/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.RationalPuncturePoint
import Nyll.SchemeTheory.ProjectiveSpace.LinearCoordinateChange
import Nyll.SchemeTheory.ProjectiveSpace.CoordinateChange

/-! # Actual rational points under projective coordinate change -/

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial

namespace AlgebraicGeometry.ProjSpace

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 2) K

/-- Pair coordinates in the same order used by the puncture equation. -/
def pairCoordinates : (K × K) ≃ₗ[K] (Fin 2 → K) where
  toFun v := ![v.1, v.2]
  invFun v := (v 0, v 1)
  left_inv v := by rfl
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' a v := by ext i; fin_cases i <;> rfl

/-- Express a pair-coordinate equivalence in indexed coordinates. -/
def finCoordinateEquiv (f : (K × K) ≃ₗ[K] (K × K)) :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) :=
  ((pairCoordinates (K := K)).symm.trans f).trans pairCoordinates

@[simp] theorem finCoordinateEquiv_pairCoordinates
    (f : (K × K) ≃ₗ[K] (K × K)) (v : K × K) :
    finCoordinateEquiv f (pairCoordinates v) = pairCoordinates (f v) := rfl

/-- Coordinate vanishing gives ideal membership at the actual rational point. -/
theorem homogeneous_mem_rationalPuncturePoint
    (v : K × K) (hv : v ≠ 0) {d : ℕ} (hd : 0 < d)
    (p : MvPolynomial (Fin 2) K) (hp : p ∈ 𝒜 d)
    (heval : MvPolynomial.eval (![v.1, v.2] : Fin 2 → K) p = 0) :
    p ∈ (rationalPuncturePoint v hv).asHomogeneousIdeal := by
  have hval : punctureEvaluationSections v p = 0 := by
    change (Scheme.ΓSpecIso (.of K)).inv.hom
      (MvPolynomial.eval (![v.1, v.2] : Fin 2 → K) p) = 0
    rw [heval, map_zero]
  have hpre : rationalPunctureSection v hv ⁻¹ᵁ Proj.basicOpen 𝒜 p = ⊥ := by
    rw [rationalPunctureSection, Proj.fromOfGlobalSections_preimage_basicOpen
      𝒜 (punctureEvaluationSections v) (punctureEvaluationSections_irrelevant v hv) hd hp, hval]
    rw [Scheme.basicOpen_zero]
  by_contra h
  have hmem : coefficientFieldPoint (K := K) ∈
      rationalPunctureSection v hv ⁻¹ᵁ Proj.basicOpen 𝒜 p := h
  rw [hpre] at hmem
  exact hmem

section
variable [Infinite K]

/-- The actual scheme map sends a rational point to its linear-coordinate image. -/
theorem linearCoordinateMap_rationalPuncturePoint
    (f : (K × K) ≃ₗ[K] (K × K)) (v : K × K) (hv : v ≠ 0) :
    linearCoordinateMap (finCoordinateEquiv f) (rationalPuncturePoint v hv) =
      rationalPuncturePoint (f v) (map_zero f ▸ f.injective.ne hv) := by
  apply eq_of_punctureForm_mem (f v) (map_zero f ▸ f.injective.ne hv)
  · have hsub : linearSubstitution (finCoordinateEquiv f).toLinearMap (punctureForm (f v)) ∈
        (rationalPuncturePoint v hv).asHomogeneousIdeal := by
      apply homogeneous_mem_rationalPuncturePoint v hv one_pos _
        ((linearSubstitution (finCoordinateEquiv f).toLinearMap).map_mem
          (punctureForm_mem_one (f v)))
      calc
        _ = MvPolynomial.eval (finCoordinateEquiv f (![v.1, v.2]))
            (punctureForm (f v)) := eval_linearSubstitution _ _ _
        _ = 0 := by
          change MvPolynomial.eval (![(f v).1, (f v).2] : Fin 2 → K)
            (punctureForm (f v)) = 0
          simp [punctureForm, mul_comm]
    by_contra hnot
    have hin : rationalPuncturePoint v hv ∈ linearCoordinateMap (finCoordinateEquiv f) ⁻¹ᵁ
        Proj.basicOpen 𝒜 (punctureForm (f v)) := hnot
    rw [linearCoordinateMap_preimage_basicOpen] at hin
    exact hin hsub
  · exact punctureForm_mem_rationalPuncturePoint _ _

/-- The scheme isomorphism attached to the same pair-coordinate linear map. -/
def pairLinearCoordinateIso (f : (K × K) ≃ₗ[K] (K × K)) : Proj 𝒜 ≅ Proj 𝒜 :=
  linearCoordinateIso (finCoordinateEquiv f)

theorem pairLinearCoordinateIso_rationalPuncturePoint
    (f : (K × K) ≃ₗ[K] (K × K)) (v : K × K) (hv : v ≠ 0) :
    (pairLinearCoordinateIso f).hom (rationalPuncturePoint v hv) =
      rationalPuncturePoint (f v) (map_zero f ▸ f.injective.ne hv) :=
  linearCoordinateMap_rationalPuncturePoint f v hv

end

/-- Representative-independent actual rational closed points. -/
def projectiveRationalPoint (p : Projectivization K (K × K)) : ProjectiveSpectrum 𝒜 :=
  rationalPuncturePoint p.rep p.rep_nonzero

@[simp] theorem projectiveRationalPoint_mk (v : K × K) (hv : v ≠ 0) :
    projectiveRationalPoint (Projectivization.mk K v hv) = rationalPuncturePoint v hv := by
  apply rationalPuncturePoint_eq_of_mk_eq
  exact (Projectivization.mk K v hv).mk_rep

theorem pairLinearCoordinateIso_projectiveRationalPoint [Infinite K]
    (f : (K × K) ≃ₗ[K] (K × K)) (p : Projectivization K (K × K)) :
    (pairLinearCoordinateIso f).hom (projectiveRationalPoint p) =
      projectiveRationalPoint (AnabelianGeometry.ProjectiveLine.projectiveLinearEquiv f p) := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [AnabelianGeometry.ProjectiveLine.projectiveLinearEquiv_mk,
      projectiveRationalPoint_mk, projectiveRationalPoint_mk]
    exact pairLinearCoordinateIso_rationalPuncturePoint f v hv

end AlgebraicGeometry.ProjSpace
