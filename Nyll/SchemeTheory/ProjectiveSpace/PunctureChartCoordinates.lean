/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.PunctureChart
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange

/-! # Actual affine-chart coordinates of a projective puncture zero -/

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open HomogeneousLocalization
open AlgebraicCurves.Geometry.Projective.Proofs
open ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "P₂" => MvPolynomial (Fin 2) K
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 2) K

/-- The numerator of a chart coordinate minus a scalar. -/
def chartCoordinateNumerator (j k : Fin 2) (t : K) : P₂ := X k - C t * X j

theorem chartCoordinateNumerator_mem_one (j k : Fin 2) (t : K) :
    chartCoordinateNumerator j k t ∈ 𝒜 1 := by
  apply (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
  exact (MvPolynomial.isHomogeneous_X K k).sub
    (MvPolynomial.isHomogeneous_C_mul_X t j)

/-- The puncture equation supplies each normalized chart numerator. -/
theorem puncture_chartCoordinateNumerator_mem
    (v : K × K) (j : Fin 2)
    (hvj : (![v.1, v.2] : Fin 2 → K) j ≠ 0)
    (p : ProjectiveSpectrum 𝒜) (hlinear : punctureForm v ∈ p.asHomogeneousIdeal)
    (k : Fin 2) :
    chartCoordinateNumerator j k
      ((![v.1, v.2] : Fin 2 → K) k / (![v.1, v.2] : Fin 2 → K) j)
      ∈ p.asHomogeneousIdeal := by
  let I : Ideal P₂ := p.asHomogeneousIdeal.toIdeal
  have hlinear' : punctureForm v ∈ I := hlinear
  change chartCoordinateNumerator j k
    ((![v.1, v.2] : Fin 2 → K) k / (![v.1, v.2] : Fin 2 → K) j) ∈ I
  fin_cases j <;> fin_cases k
  · have hv0 : v.1 ≠ 0 := hvj
    change X 0 - C (v.1 / v.1) * X 0 ∈ I
    rw [div_self hv0, map_one, one_mul, sub_self]
    exact I.zero_mem
  · have hv0 : v.1 ≠ 0 := hvj
    have h := I.mul_mem_left (C (v.1)⁻¹) (I.neg_mem hlinear')
    have heq : C (v.1)⁻¹ * (-punctureForm v) =
        chartCoordinateNumerator 0 1 (v.2 / v.1) := by
      change C (v.1)⁻¹ * (-(C v.2 * X 0 - C v.1 * X 1)) =
        X 1 - C (v.2 / v.1) * X 0
      simp only [neg_sub, mul_sub, ← mul_assoc, ← map_mul]
      rw [inv_mul_cancel₀ hv0, map_one, one_mul]
      simp only [div_eq_mul_inv, mul_comm]
    rw [heq] at h
    exact h
  · have hv1 : v.2 ≠ 0 := hvj
    have h := I.mul_mem_left (C (v.2)⁻¹) hlinear'
    have heq : C (v.2)⁻¹ * punctureForm v =
        chartCoordinateNumerator 1 0 (v.1 / v.2) := by
      change C (v.2)⁻¹ * (C v.2 * X 0 - C v.1 * X 1) =
        X 0 - C (v.1 / v.2) * X 1
      simp only [mul_sub, ← mul_assoc, ← map_mul]
      rw [inv_mul_cancel₀ hv1, map_one, one_mul]
      simp only [div_eq_mul_inv, mul_comm]
    rw [heq] at h
    exact h
  · have hv1 : v.2 ≠ 0 := hvj
    change X 1 - C (v.2 / v.2) * X 1 ∈ I
    rw [div_self hv1, map_one, one_mul, sub_self]
    exact I.zero_mem

/-- The degree-zero fraction is the chart coordinate minus its scalar. -/
theorem ratio_sub_eq_isLocalizationElem (j k : Fin 2) (t : K) :
    ratio K 1 j k - algebraMap K (Away 𝒜 (X j)) t =
      Away.isLocalizationElem (X_mem_one K 1 j)
        (chartCoordinateNumerator_mem_one j k t) := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (X j : P₂))
  simp only [Away.isLocalizationElem, ratio, HomogeneousLocalization.val_sub,
    Away.val_mk, val_algebraMap, pow_one]
  rw [← Localization.mk_one_eq_algebraMap, Localization.sub_mk]
  simp only [Submonoid.coe_one, one_mul, mul_one]
  congr 1
  simp only [chartCoordinateNumerator, mul_comm]

/-- The prime furnished by the actual standard scheme chart. -/
def standardChartPrime (j : Fin 2) (x : (Proj.basicOpen 𝒜 (X j)).toScheme) :
    PrimeSpectrum (Away 𝒜 (X j)) :=
  (Proj.basicOpenIsoSpec 𝒜 (X j) (X_mem_one K 1 j) one_pos).hom x

theorem awayι_standardChartPrime (j : Fin 2)
    (x : (Proj.basicOpen 𝒜 (X j)).toScheme) :
    Proj.awayι 𝒜 (X j) (X_mem_one K 1 j) one_pos (standardChartPrime j x) = x.val := by
  let E := Proj.basicOpenIsoSpec 𝒜 (X j) (X_mem_one K 1 j) one_pos
  have hcomp : E.hom ≫ Proj.awayι 𝒜 (X j) (X_mem_one K 1 j) one_pos =
      (Proj.basicOpen 𝒜 (X j)).ι := by
    change E.hom ≫ (E.inv ≫ (Proj.basicOpen 𝒜 (X j)).ι) =
      (Proj.basicOpen 𝒜 (X j)).ι
    exact E.hom_inv_id_assoc _
  calc
    _ = (E.hom ≫ Proj.awayι 𝒜 (X j) (X_mem_one K 1 j) one_pos) x :=
      (Scheme.Hom.comp_apply E.hom
        (Proj.awayι 𝒜 (X j) (X_mem_one K 1 j) one_pos) x).symm
    _ = (Proj.basicOpen 𝒜 (X j)).ι x :=
      congrArg (fun f : (Proj.basicOpen 𝒜 (X j)).toScheme ⟶ Proj 𝒜 => f x) hcomp
    _ = x.val := Scheme.Opens.ι_apply (Proj.basicOpen 𝒜 (X j)) x

/-- Numerator membership transports to the actual standard chart prime. -/
theorem isLocalizationElem_mem_standardChartPrime
    (j : Fin 2) (x : (Proj.basicOpen 𝒜 (X j)).toScheme)
    (g : P₂) (hg : g ∈ 𝒜 1) (hmem : g ∈ x.val.asHomogeneousIdeal) :
    Away.isLocalizationElem (X_mem_one K 1 j) hg ∈
      (standardChartPrime j x).asIdeal := by
  by_contra hnot
  have hq : standardChartPrime j x ∈
      PrimeSpectrum.basicOpen (Away.isLocalizationElem (X_mem_one K 1 j) hg) := hnot
  have hp : Proj.awayι 𝒜 (X j) (X_mem_one K 1 j) one_pos (standardChartPrime j x) ∈
      Proj.basicOpen 𝒜 g := by
    let q : Spec (CommRingCat.of (Away 𝒜 (X j))) := standardChartPrime j x
    have hU : Proj.awayι 𝒜 (X j) (X_mem_one K 1 j) one_pos ⁻¹ᵁ
        Proj.basicOpen 𝒜 g =
        PrimeSpectrum.basicOpen (Away.isLocalizationElem (X_mem_one K 1 j) hg) :=
      Proj.awayι_preimage_basicOpen 𝒜 (X_mem_one K 1 j) one_pos hg one_pos
    have hq' : q ∈ (PrimeSpectrum.basicOpen
        (Away.isLocalizationElem (X_mem_one K 1 j) hg) :
          (Spec (CommRingCat.of (Away 𝒜 (X j)))).Opens) := hq
    have hpre : q ∈ (Proj.awayι 𝒜 (X j) (X_mem_one K 1 j) one_pos ⁻¹ᵁ
        Proj.basicOpen 𝒜 g) :=
      Eq.mpr (congrArg
        (fun U : (Spec (CommRingCat.of (Away 𝒜 (X j)))).Opens => q ∈ U) hU) hq'
    exact hpre
  rw [awayι_standardChartPrime] at hp
  change g ∉ x.val.asHomogeneousIdeal at hp
  exact hp hmem

/-- The puncture zero has its prescribed coordinate in the actual affine chart. -/
theorem linearForm_zero_chart_coordinate
    (v : K × K) (j : Fin 2) (hvj : (![v.1, v.2] : Fin 2 → K) j ≠ 0)
    (x : (Proj.basicOpen 𝒜 (X j)).toScheme)
    (hlinear : punctureForm v ∈ x.val.asHomogeneousIdeal) (k : Fin 2) :
    ratio K 1 j k - algebraMap K (Away 𝒜 (X j))
      ((![v.1, v.2] : Fin 2 → K) k / (![v.1, v.2] : Fin 2 → K) j) ∈
      (standardChartPrime j x).asIdeal := by
  rw [ratio_sub_eq_isLocalizationElem]
  exact isLocalizationElem_mem_standardChartPrime j x _
    (chartCoordinateNumerator_mem_one j k _)
    (puncture_chartCoordinateNumerator_mem v j hvj x.val hlinear k)

theorem linearForm_zero_chart_coordinate_of_point
    (v : K × K) (j : Fin 2) (hvj : (![v.1, v.2] : Fin 2 → K) j ≠ 0)
    (p : ProjectiveSpectrum 𝒜) (hlinear : punctureForm v ∈ p.asHomogeneousIdeal)
    (k : Fin 2) :
    let x : (Proj.basicOpen 𝒜 (X j)).toScheme :=
      ⟨p, linearForm_zero_implies_chart v j hvj p hlinear⟩
    ratio K 1 j k - algebraMap K (Away 𝒜 (X j))
      ((![v.1, v.2] : Fin 2 → K) k / (![v.1, v.2] : Fin 2 → K) j) ∈
      (standardChartPrime j x).asIdeal := by
  intro x
  exact linearForm_zero_chart_coordinate v j hvj x hlinear k

theorem linearForm_zero_chart_polynomial_coordinate
    (v : K × K) (j : Fin 2) (hvj : (![v.1, v.2] : Fin 2 → K) j ≠ 0)
    (x : (Proj.basicOpen 𝒜 (X j)).toScheme)
    (hlinear : punctureForm v ∈ x.val.asHomogeneousIdeal) (k : {k : Fin 2 // k ≠ j}) :
    awayChartEquiv (S := K) 1 j (MvPolynomial.X k) -
      algebraMap K (Away 𝒜 (X j))
        ((![v.1, v.2] : Fin 2 → K) k.val / (![v.1, v.2] : Fin 2 → K) j) ∈
      (standardChartPrime j x).asIdeal := by
  rw [awayChartEquiv_X]
  exact linearForm_zero_chart_coordinate v j hvj x hlinear k.val

end AlgebraicGeometry.ProjSpace
