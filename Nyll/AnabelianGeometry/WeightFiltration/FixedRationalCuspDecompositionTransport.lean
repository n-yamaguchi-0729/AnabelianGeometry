/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalCuspDecomposition

/-! # Decomposition transport for the already fixed arithmetic witnesses

This forwarding theorem retains the existing eP, eΔ, σ and original inertia
witnesses. It never calls an existential arithmetic-recognition theorem again.
Thus the previously selected pair functions, finite-cover units and scalar
radicals can use these decomposition images without changing any choices.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open AlgebraicGeometry.ProjSpace

namespace AnabelianGeometry.WeightFiltration

/-- Add actual decomposition correspondence to the already obtained inertia
correspondence, retaining the same geometric equivalence and puncture bijection. -/
theorem rationalConfigurationChosenDecomposition_map_of_fixed_punctureEquiv
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (eP : rationalConfigurationArithmeticGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ω₂)
    (eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationGeometricGroup k κ t Ω₂)
    (heΔ : ∀ v, rationalConfigurationGeometricInclusion k κ t Ω₂ (eΔ v) =
      eP (rationalConfigurationGeometricInclusion k κ s Ω₁ v))
    (σ : s ≃ t)
    (hI : ∀ p : s, ∃ a : rationalConfigurationGeometricGroup k κ t Ω₂,
      (rationalConfigurationChosenInertia k κ s Ω₁
        (rationalConfigurationBoundaryPlace k κ s p)).map eΔ.toMonoidHom =
      (rationalConfigurationChosenInertia k κ t Ω₂
        (rationalConfigurationBoundaryPlace k κ t (σ p))).map
          (MulAut.conj a).toMonoidHom) :
    ∀ p : s, ∃ a : rationalConfigurationGeometricGroup k κ t Ω₂,
      (rationalConfigurationChosenInertia k κ s Ω₁
        (rationalConfigurationBoundaryPlace k κ s p)).map eΔ.toMonoidHom =
      (rationalConfigurationChosenInertia k κ t Ω₂
        (rationalConfigurationBoundaryPlace k κ t (σ p))).map
          (MulAut.conj a).toMonoidHom ∧
      (rationalConfigurationChosenDecomposition k κ s Ω₁
        (rationalConfigurationBoundaryPlace k κ s p)).map eP.toMonoidHom =
      (rationalConfigurationChosenDecomposition k κ t Ω₂
        (rationalConfigurationBoundaryPlace k κ t (σ p))).map
          (MulAut.conj (rationalConfigurationGeometricInclusion k κ t Ω₂ a)).toMonoidHom := by
  intro p
  obtain ⟨a, ha⟩ := hI p
  exact ⟨a, ha, rationalConfigurationChosenDecomposition_map_of_inertia
    k κ s t hs ht Ω₁ Ω₂ eP eΔ heΔ
    (rationalConfigurationBoundaryPlace k κ s p)
    (rationalConfigurationBoundaryPlace k κ t (σ p)) a ha⟩

end AnabelianGeometry.WeightFiltration
