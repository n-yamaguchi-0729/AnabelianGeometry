/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.CoherentLiftedCyclicClasses

/-! # Cyclic cross-ratio classes for a fixed geometric equivalence -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open AnabelianGeometry.ProjectiveLine
namespace AnabelianGeometry.WeightFiltration
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

/-- The geometric equivalence already constructed from the named cover square
is retained. A single lifted puncture correspondence simultaneously supplies
its actual inertia conjugacies and every cyclic cross-ratio class. -/
theorem bare_rationalConfiguration_crossRatio_cyclic_classes_fixed_geometric
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
    (hP : ∀ γ,
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ t Ω₂) (eP γ) =
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ s Ω₁) γ)
    (eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationGeometricGroup k κ t Ω₂)
    (hΔ : ∀ v, rationalConfigurationGeometricInclusion k κ t Ω₂ (eΔ v) =
      eP (rationalConfigurationGeometricInclusion k κ s Ω₁ v)) :
    ∃ τ : s ≃ t,
      (∀ p : s, ∃ a : rationalConfigurationGeometricGroup k κ t Ω₂,
        (rationalConfigurationChosenInertia k κ s Ω₁
          (rationalConfigurationBoundaryPlace k κ s p)).map eΔ.toMonoidHom =
        (rationalConfigurationChosenInertia k κ t Ω₂
          (rationalConfigurationBoundaryPlace k κ t (τ p))).map
            (MulAut.conj a).toMonoidHom) ∧
      (∀ (a b c₀ c : s), a ≠ b →
      c₀ ≠ a → c₀ ≠ b → c ≠ a → c ≠ b →
      ∃ A B : kˣ,
        (A : k) = crossRatio a.val b.val c₀.val c.val ∧
        (B : k) = crossRatio (τ a).val (τ b).val (τ c₀).val (τ c).val ∧
        Subgroup.zpowers A = Subgroup.zpowers B) := by
  obtain ⟨eΔ', hΔ', τ, hτ, hclasses⟩ :=
    bare_rationalConfiguration_crossRatio_cyclic_classes_with_inertia
      k κ s t hs ht Ω₁ Ω₂ eP hP
  have he : eΔ' = eΔ := by
    apply ContinuousMulEquiv.ext
    intro x
    let E := geometricFundamentalGroupKernelEquiv k κ
      (rationalConfigurationOpen t : Scheme)
      ((rationalConfigurationOpen t).ι ≫ π k 1)
      ((rationalConfigurationGeometricScheme k κ t).genericExtensionMorphism Ω₂)
    apply E.injective
    apply Subtype.ext
    exact (hΔ' x).trans (hΔ x).symm
  subst eΔ'
  exact ⟨τ, hτ, hclasses⟩

end AnabelianGeometry.WeightFiltration
