/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.ArithmeticCorrectionBoundaryTransport
import Nyll.AnabelianGeometry.WeightFiltration.RationalConfigurationRangeFixed

/-! # Remove the finite arithmetic correction without changing the cusp bijection

The split reconstruction supplies the actual cusp correspondence up to geometric
conjugacy. Abelianization removes that geometric conjugacy. The remaining
arithmetic correction is removed using the cyclotomic stability of every actual
rational puncture, retaining exactly the same cusp correspondence.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open AlgebraicGeometry.ProjSpace AlgebraicCurve ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

/-- The same cusp correspondence survives removal of the arithmetic correction.
No fixed-range or Galois-equivariance hypothesis is imposed on the cusps. -/
theorem rationalConfiguration_remove_arithmetic_correction_same_cusps
    (k κ : Type) [Field k] [CharZero k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k)))
    (Ωs Ωt : Type) [Field Ωs] [Field Ωt] [IsAlgClosed Ωs] [IsAlgClosed Ωt]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ωs]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ωt]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ωs]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ωt]
    (β : rationalConfigurationArithmeticGroup k κ s Ωs ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ωt)
    (e : rationalConfigurationGeometricGroup k κ s Ωs ≃ₜ*
      rationalConfigurationGeometricGroup k κ t Ωt)
    (c : rationalConfigurationArithmeticGroup k κ t Ωt)
    (he : ∀ v, rationalConfigurationGeometricInclusion k κ t Ωt (e v) =
      c * β (rationalConfigurationGeometricInclusion k κ s Ωs v) * c⁻¹)
    (τ : (projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ s) ≃
      (projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ t))
    (hτ : ∀ p, ∃ a : rationalConfigurationGeometricGroup k κ t Ωt,
      (rationalConfigurationChosenInertia k κ s Ωs p).map e.toMonoidHom =
        (rationalConfigurationChosenInertia k κ t Ωt (τ p)).map
          (MulAut.conj a).toMonoidHom) :
    ∃ e₀ : rationalConfigurationGeometricGroup k κ s Ωs ≃ₜ*
        rationalConfigurationGeometricGroup k κ t Ωt,
      (∀ v, rationalConfigurationGeometricInclusion k κ t Ωt (e₀ v) =
        β (rationalConfigurationGeometricInclusion k κ s Ωs v)) ∧
      ∀ p,
        ((rationalConfigurationChosenInertia k κ s Ωs p).map
          (TopologicalAbelianization.mk (rationalConfigurationGeometricGroup k κ s Ωs))).map
            (TopologicalAbelianization.congr e₀).toMonoidHom =
          (rationalConfigurationChosenInertia k κ t Ωt (τ p)).map
            (TopologicalAbelianization.mk (rationalConfigurationGeometricGroup k κ t Ωt)) := by
  let : IsSepClosure k κ := inferInstance
  let b := β.toMonoidHom.comp (rationalConfigurationGeometricInclusion k κ s Ωs).toMonoidHom
  obtain ⟨e₀, he₀, hkeep⟩ := exists_geometricEquiv_remove_arithmetic_correction
    k κ (rationalConfigurationOpen t : Scheme)
    ((rationalConfigurationOpen t).ι ≫ π k 1)
    ((rationalConfigurationGeometricScheme k κ t).genericExtensionMorphism Ωt)
    b e c he
  refine ⟨e₀, he₀, ?_⟩
  intro p
  apply hkeep
  · obtain ⟨a, ha⟩ := hτ p
    have hmk : (TopologicalAbelianization.congr e).toMonoidHom.comp
        (TopologicalAbelianization.mk (rationalConfigurationGeometricGroup k κ s Ωs)) =
      (TopologicalAbelianization.mk (rationalConfigurationGeometricGroup k κ t Ωt)).comp
        e.toMonoidHom := by
      apply MonoidHom.ext
      intro v
      exact TopologicalAbelianization.congr_apply_mk e v
    have hconj : (TopologicalAbelianization.mk
          (rationalConfigurationGeometricGroup k κ t Ωt)).comp
          (MulAut.conj a).toMonoidHom =
        TopologicalAbelianization.mk (rationalConfigurationGeometricGroup k κ t Ωt) := by
      apply MonoidHom.ext
      intro v
      change TopologicalAbelianization.mk _ (a * v * a⁻¹) = _
      rw [map_mul, map_mul, map_inv,
        mul_comm (TopologicalAbelianization.mk _ a) (TopologicalAbelianization.mk _ v),
        mul_assoc, mul_inv_cancel, mul_one]
    rw [Subgroup.map_map, hmk, ← Subgroup.map_map, ha, Subgroup.map_map, hconj]
  · exact rationalConfigurationChosenInertia_abelian_range_galois_fixed
      k κ t Ωt (τ p)
      (arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ t Ωt) c)


/-- The label form returned by the split reconstruction theorem. The boundary
bijection is the one induced by the very same puncture permutation. -/
theorem rationalConfiguration_remove_arithmetic_correction_same_punctures
    (k κ : Type) [Field k] [CharZero k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k)))
    (Ωs Ωt : Type) [Field Ωs] [Field Ωt] [IsAlgClosed Ωs] [IsAlgClosed Ωt]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ωs]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ωt]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ωs]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ωt]
    (β : rationalConfigurationArithmeticGroup k κ s Ωs ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ωt)
    (e : rationalConfigurationGeometricGroup k κ s Ωs ≃ₜ*
      rationalConfigurationGeometricGroup k κ t Ωt)
    (c : rationalConfigurationArithmeticGroup k κ t Ωt)
    (he : ∀ v, rationalConfigurationGeometricInclusion k κ t Ωt (e v) =
      c * β (rationalConfigurationGeometricInclusion k κ s Ωs v) * c⁻¹)
    (σ : s ≃ t)
    (hσ : ∀ p : s, ∃ a : rationalConfigurationGeometricGroup k κ t Ωt,
      (rationalConfigurationChosenInertia k κ s Ωs
        (rationalConfigurationBoundaryPlace k κ s p)).map e.toMonoidHom =
      (rationalConfigurationChosenInertia k κ t Ωt
        (rationalConfigurationBoundaryPlace k κ t (σ p))).map
          (MulAut.conj a).toMonoidHom) :
    let τ := (rationalConfigurationBoundaryPlaceEquiv k κ s).symm.trans
      (σ.trans (rationalConfigurationBoundaryPlaceEquiv k κ t))
    ∃ e₀ : rationalConfigurationGeometricGroup k κ s Ωs ≃ₜ*
        rationalConfigurationGeometricGroup k κ t Ωt,
      (∀ v, rationalConfigurationGeometricInclusion k κ t Ωt (e₀ v) =
        β (rationalConfigurationGeometricInclusion k κ s Ωs v)) ∧
      ∀ p,
        ((rationalConfigurationChosenInertia k κ s Ωs p).map
          (TopologicalAbelianization.mk (rationalConfigurationGeometricGroup k κ s Ωs))).map
            (TopologicalAbelianization.congr e₀).toMonoidHom =
          (rationalConfigurationChosenInertia k κ t Ωt (τ p)).map
            (TopologicalAbelianization.mk (rationalConfigurationGeometricGroup k κ t Ωt)) := by
  intro τ
  apply rationalConfiguration_remove_arithmetic_correction_same_cusps
    k κ s t Ωs Ωt β e c he τ
  intro p
  obtain ⟨x, rfl⟩ := (rationalConfigurationBoundaryPlaceEquiv k κ s).surjective p
  have hτ : τ (rationalConfigurationBoundaryPlaceEquiv k κ s x) =
      rationalConfigurationBoundaryPlaceEquiv k κ t (σ x) := by
    change rationalConfigurationBoundaryPlaceEquiv k κ t
      (σ ((rationalConfigurationBoundaryPlaceEquiv k κ s).symm
        (rationalConfigurationBoundaryPlaceEquiv k κ s x))) = _
    rw [Equiv.symm_apply_apply]
  rw [hτ]
  exact hσ x

end AnabelianGeometry.WeightFiltration
