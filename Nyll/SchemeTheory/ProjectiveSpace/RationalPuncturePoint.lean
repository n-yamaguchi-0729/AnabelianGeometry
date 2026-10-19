/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.PunctureChartCoordinates
import Nyll.SchemeTheory.ProjectiveSpace.ChartPrimeCoordinateUniqueness

/-! # The actual rational point cut out by a homogeneous puncture equation -/

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicCurves.Geometry.Projective.Proofs
open ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "P₂" => MvPolynomial (Fin 2) K
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 2) K

theorem exists_nonzero_puncture_coordinate (v : K × K) (hv : v ≠ 0) :
    ∃ j : Fin 2, (![v.1, v.2] : Fin 2 → K) j ≠ 0 := by
  by_cases h : v.1 = 0
  · refine ⟨1, ?_⟩
    intro h'
    apply hv
    apply Prod.ext
    · exact h
    · exact h'
  · exact ⟨0, h⟩

/-- The homogeneous puncture equation has at most one projective zero. -/
theorem eq_of_punctureForm_mem (v : K × K) (hv : v ≠ 0)
    (p q : ProjectiveSpectrum 𝒜)
    (hp : punctureForm v ∈ p.asHomogeneousIdeal)
    (hq : punctureForm v ∈ q.asHomogeneousIdeal) : p = q := by
  obtain ⟨j, hj⟩ := exists_nonzero_puncture_coordinate v hv
  let xp : (Proj.basicOpen 𝒜 (X j)).toScheme :=
    ⟨p, linearForm_zero_implies_chart v j hj p hp⟩
  let xq : (Proj.basicOpen 𝒜 (X j)).toScheme :=
    ⟨q, linearForm_zero_implies_chart v j hj q hq⟩
  let E := awayChartEquiv (S := K) 1 j
  let t : {k : Fin 2 // k ≠ j} → K := fun k =>
    (![v.1, v.2] : Fin 2 → K) k.val / (![v.1, v.2] : Fin 2 → K) j
  have he : standardChartPrime j xp = standardChartPrime j xq := by
    apply PrimeSpectrum.ext
    apply prime_eq_of_coordinateValues E
      (standardChartPrime j xp).asIdeal (standardChartPrime j xq).asIdeal t
    · intro k
      exact linearForm_zero_chart_polynomial_coordinate v j hj xp hp k
    · intro k
      exact linearForm_zero_chart_polynomial_coordinate v j hj xq hq k
  have h := congrArg (fun z => Proj.awayι 𝒜 (X j) (X_mem_one K 1 j) one_pos z) he
  have hp' := awayι_standardChartPrime j xp
  have hq' := awayι_standardChartPrime j xq
  exact hp'.symm.trans (h.trans hq')

/-- Coordinates evaluated as global sections of the coefficient spectrum. -/
def punctureEvaluationSections (v : K × K) : P₂ →+* Γ(Spec (.of K), ⊤) :=
  (Scheme.ΓSpecIso (.of K)).inv.hom.comp
    (MvPolynomial.eval (![v.1, v.2] : Fin 2 → K))

theorem punctureEvaluationSections_irrelevant (v : K × K) (hv : v ≠ 0) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (punctureEvaluationSections v) = ⊤ := by
  obtain ⟨j, hj⟩ := exists_nonzero_puncture_coordinate v hv
  let g : K →+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).inv.hom
  let a : K := (![v.1, v.2] : Fin 2 → K) j
  let I : Ideal Γ(Spec (.of K), ⊤) :=
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (punctureEvaluationSections v)
  have ha : a ≠ 0 := hj
  have hX : (X j : P₂) ∈ HomogeneousIdeal.irrelevant 𝒜 :=
    HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 one_pos (X_mem_one K 1 j)
  have hmem : g a ∈ I := by
    have h := Ideal.mem_map_of_mem (punctureEvaluationSections v) hX
    simpa only [punctureEvaluationSections, RingHom.comp_apply, MvPolynomial.eval_X,
      I, g, a] using h
  have hmul := I.mul_mem_left (g a⁻¹) hmem
  have hone : (1 : Γ(Spec (.of K), ⊤)) ∈ I := by
    simpa only [← map_mul, inv_mul_cancel₀ ha, map_one] using hmul
  exact I.eq_top_iff_one.mpr hone

/-- The actual rational section determined by nonzero homogeneous coordinates. -/
def rationalPunctureSection (v : K × K) (hv : v ≠ 0) : Spec (.of K) ⟶ Proj 𝒜 :=
  Proj.fromOfGlobalSections 𝒜 (punctureEvaluationSections v)
    (punctureEvaluationSections_irrelevant v hv)

theorem rationalPunctureSection_comp_π (v : K × K) (hv : v ≠ 0) :
    rationalPunctureSection v hv ≫ π K 1 = 𝟙 _ := by
  have hconst : ((punctureEvaluationSections v).comp (algebraMap (𝒜 0) P₂)).comp
      (grad0Equiv K 1).toRingHom = (Scheme.ΓSpecIso (.of K)).inv.hom := by
    ext a
    change (Scheme.ΓSpecIso (.of K)).inv.hom
      (MvPolynomial.eval (![v.1, v.2] : Fin 2 → K) (C a)) =
      (Scheme.ΓSpecIso (.of K)).inv.hom a
    rw [MvPolynomial.eval_C]
  rw [rationalPunctureSection, π, ← Category.assoc, Proj.fromOfGlobalSections_toSpecZero]
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hconst]
  exact toSpecΓ_SpecMap_ΓSpecIso_inv (.of K)

/-- The sole point of the coefficient field spectrum. -/
def coefficientFieldPoint : Spec (.of K) := ⟨⊥, inferInstance⟩

/-- The underlying point of the constructed rational section. -/
def rationalPuncturePoint (v : K × K) (hv : v ≠ 0) : ProjectiveSpectrum 𝒜 :=
  rationalPunctureSection v hv (coefficientFieldPoint (K := K))

theorem punctureForm_mem_one (v : K × K) : punctureForm v ∈ 𝒜 1 := by
  apply (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
  exact (MvPolynomial.isHomogeneous_C_mul_X v.2 0).sub
    (MvPolynomial.isHomogeneous_C_mul_X v.1 1)

theorem punctureEvaluationSections_punctureForm (v : K × K) :
    punctureEvaluationSections v (punctureForm v) = 0 := by
  have heval : MvPolynomial.eval (![v.1, v.2] : Fin 2 → K) (punctureForm v) = 0 := by
    rw [punctureForm, map_sub, map_mul, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_C, MvPolynomial.eval_X, MvPolynomial.eval_X]
    change v.2 * v.1 - v.1 * v.2 = 0
    rw [mul_comm v.2 v.1, sub_self]
  change (Scheme.ΓSpecIso (.of K)).inv.hom
    (MvPolynomial.eval (![v.1, v.2] : Fin 2 → K) (punctureForm v)) = 0
  rw [heval, map_zero]

/-- The actual section point is a zero of its puncture equation. -/
theorem punctureForm_mem_rationalPuncturePoint (v : K × K) (hv : v ≠ 0) :
    punctureForm v ∈ (rationalPuncturePoint v hv).asHomogeneousIdeal := by
  have hpre : rationalPunctureSection v hv ⁻¹ᵁ Proj.basicOpen 𝒜 (punctureForm v) = ⊥ := by
    rw [rationalPunctureSection, Proj.fromOfGlobalSections_preimage_basicOpen
      𝒜 (punctureEvaluationSections v) (punctureEvaluationSections_irrelevant v hv)
      one_pos (punctureForm_mem_one v), punctureEvaluationSections_punctureForm]
    exact (Spec (.of K)).basicOpen_zero ⊤
  by_contra h
  have hmem : coefficientFieldPoint (K := K) ∈
      rationalPunctureSection v hv ⁻¹ᵁ Proj.basicOpen 𝒜 (punctureForm v) := h
  rw [hpre] at hmem
  exact hmem

/-- The linear equation cuts out exactly its actual rational closed point. -/
theorem zeroLocus_punctureForm_eq_singleton (v : K × K) (hv : v ≠ 0) :
    ProjectiveSpectrum.zeroLocus 𝒜 {punctureForm v} = {rationalPuncturePoint v hv} := by
  ext p
  constructor
  · intro hp
    have hp' : punctureForm v ∈ p.asHomogeneousIdeal := hp (Set.mem_singleton _)
    exact Set.mem_singleton_iff.mpr (eq_of_punctureForm_mem v hv
      p (rationalPuncturePoint v hv) hp' (punctureForm_mem_rationalPuncturePoint v hv))
  · intro hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    intro f hf
    rcases Set.mem_singleton_iff.mp hf with rfl
    exact punctureForm_mem_rationalPuncturePoint v hv

theorem isClosed_singleton_rationalPuncturePoint (v : K × K) (hv : v ≠ 0) :
    IsClosed ({rationalPuncturePoint v hv} : Set (ProjectiveSpectrum 𝒜)) := by
  rw [← zeroLocus_punctureForm_eq_singleton v hv]
  exact ProjectiveSpectrum.isClosed_zeroLocus 𝒜 _

theorem rationalPuncturePoint_eq_of_mk_eq (v w : K × K) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : Projectivization.mk K v hv = Projectivization.mk K w hw) :
    rationalPuncturePoint v hv = rationalPuncturePoint w hw := by
  have hU := basicOpen_punctureForm_eq_of_mk_eq v w hv hw h
  have hmem : punctureForm w ∈ (rationalPuncturePoint v hv).asHomogeneousIdeal := by
    by_contra hnot
    have hin : rationalPuncturePoint v hv ∈ Proj.basicOpen 𝒜 (punctureForm w) := hnot
    rw [← hU] at hin
    exact hin (punctureForm_mem_rationalPuncturePoint v hv)
  exact eq_of_punctureForm_mem w hw (rationalPuncturePoint v hv)
    (rationalPuncturePoint w hw) hmem (punctureForm_mem_rationalPuncturePoint w hw)

end AlgebraicGeometry.ProjSpace
