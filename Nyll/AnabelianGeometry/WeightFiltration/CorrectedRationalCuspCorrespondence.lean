/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.ArithmeticCorrectionRationalCuspInertia

/-! # Corrected rational cusp correspondence -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups SchemeTheory
namespace AnabelianGeometry.WeightFiltration

private theorem corrected_map_of_conjugate
    {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    (α α' : G ≃ₜ* H) (I : Subgroup G) (J : Subgroup H) (a g : H)
    (hI : I.map α.toMonoidHom = J.map (MulAut.conj a).toMonoidHom)
    (hJ : J.map (α'.toMonoidHom.comp α.symm.toMonoidHom) =
      J.map (MulAut.conj g).toMonoidHom) :
    I.map α'.toMonoidHom =
      J.map (MulAut.conj (α' (α.symm a) * g)).toMonoidHom := by
  let θ : H →* H := α'.toMonoidHom.comp α.symm.toMonoidHom
  have hcomp : θ.comp α.toMonoidHom = α'.toMonoidHom := by
    ext x
    exact congrArg α' (α.symm_apply_apply x)
  have hconj : θ.comp (MulAut.conj a).toMonoidHom =
      (MulAut.conj (θ a)).toMonoidHom.comp θ := by
    ext x
    change θ (a * x * a⁻¹) = θ a * θ x * (θ a)⁻¹
    rw [map_mul, map_mul, map_inv]
  calc
    I.map α'.toMonoidHom = (I.map α.toMonoidHom).map θ := by
      rw [Subgroup.map_map, hcomp]
    _ = (J.map (MulAut.conj a).toMonoidHom).map θ := congrArg (fun K => K.map θ) hI
    _ = (J.map θ).map (MulAut.conj (θ a)).toMonoidHom := by
      rw [Subgroup.map_map, hconj, Subgroup.map_map]
    _ = (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (θ a)).toMonoidHom :=
      congrArg (fun K => K.map (MulAut.conj (θ a)).toMonoidHom) hJ
    _ = J.map (MulAut.conj (α' (α.symm a) * g)).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      change θ a * (g * x * g⁻¹) * (θ a)⁻¹ =
        (θ a * g) * x * (θ a * g)⁻¹
      simp only [mul_inv_rev, mul_assoc]

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower

theorem rationalConfiguration_corrected_geometricMap_same_punctures
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k))) (ht : 3 ≤ t.card)
    (Ωs Ωt : Type) [Field Ωs] [Field Ωt] [IsAlgClosed Ωs] [IsAlgClosed Ωt]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ωs]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ωt]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ωs]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ωt]
    (α α' : rationalConfigurationGeometricGroup k κ s Ωs ≃ₜ*
      rationalConfigurationGeometricGroup k κ t Ωt)
    (σ : s ≃ t)
    (hI : ∀ p : s, ∃ a : rationalConfigurationGeometricGroup k κ t Ωt,
      (rationalConfigurationChosenInertia k κ s Ωs
        (rationalConfigurationBoundaryPlace k κ s p)).map α.toMonoidHom =
      (rationalConfigurationChosenInertia k κ t Ωt
        (rationalConfigurationBoundaryPlace k κ t (σ p))).map
          (MulAut.conj a).toMonoidHom)
    (c : rationalConfigurationArithmeticGroup k κ t Ωt)
    (hc : ∀ x, rationalConfigurationGeometricInclusion k κ t Ωt (α' x) =
      c * rationalConfigurationGeometricInclusion k κ t Ωt (α x) * c⁻¹) :
    ∀ p : s, ∃ a : rationalConfigurationGeometricGroup k κ t Ωt,
      (rationalConfigurationChosenInertia k κ s Ωs
        (rationalConfigurationBoundaryPlace k κ s p)).map α'.toMonoidHom =
      (rationalConfigurationChosenInertia k κ t Ωt
        (rationalConfigurationBoundaryPlace k κ t (σ p))).map
          (MulAut.conj a).toMonoidHom := by
  intro p
  obtain ⟨a, ha⟩ := hI p
  let θ := α'.toMonoidHom.comp α.symm.toMonoidHom
  have hθ : ∀ x, rationalConfigurationGeometricInclusion k κ t Ωt (θ x) =
      c * rationalConfigurationGeometricInclusion k κ t Ωt x * c⁻¹ := by
    intro x
    change rationalConfigurationGeometricInclusion k κ t Ωt (α' (α.symm x)) = _
    rw [hc, α.apply_symm_apply]
  obtain ⟨g, hg⟩ := rationalConfiguration_arithmeticCorrection_geometricInertia
    k κ t ht Ωt (rationalConfigurationBoundaryPlace k κ t (σ p)) c θ hθ
  exact ⟨α' (α.symm a) * g, corrected_map_of_conjugate α α' _ _ a g ha hg⟩

end AnabelianGeometry.WeightFiltration
