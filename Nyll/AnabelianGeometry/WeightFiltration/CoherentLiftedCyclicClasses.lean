/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalCrossRatioWithInertia

/-! # Cyclic cross ratios for a prescribed coherent puncture equivalence

The arithmetic lift and inertia correspondence determine both geometric map
and puncture equivalence uniquely. Thus all cyclic classes can be exported for
an already retained lifted τ. No independent root signs, field map, or new
puncture correspondence is assumed. The proof's temporary existential witness
is identified with the given τ before any cross-ratio data are returned.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open AnabelianGeometry.ProjectiveLine
namespace AnabelianGeometry.WeightFiltration
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

private theorem coherent_conjugate_twice
    {G : Type*} [Group G] (A : Subgroup G) (a b : G) :
    (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      A.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change b * (a * x * a⁻¹) * b⁻¹ = (b * a) * x * (b * a)⁻¹
  simp only [mul_inv_rev, mul_assoc]

/-- A fixed group isomorphism has at most one inertia-label correspondence
when the target's inertia conjugacy classes distinguish its labels. -/
theorem inertiaLabelEquiv_unique
    {P Q G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (I : P → Subgroup G) (J : Q → Subgroup H)
    (σ τ : P ≃ Q)
    (hσ : ∀ p, ∃ a, (I p).map e.toMonoidHom =
      (J (σ p)).map (MulAut.conj a).toMonoidHom)
    (hτ : ∀ p, ∃ b, (I p).map e.toMonoidHom =
      (J (τ p)).map (MulAut.conj b).toMonoidHom)
    (hsep : ∀ p q a, J p = (J q).map (MulAut.conj a).toMonoidHom → p = q) :
    σ = τ := by
  apply Equiv.ext
  intro p
  obtain ⟨a, ha⟩ := hσ p
  obtain ⟨b, hb⟩ := hτ p
  have h := congrArg
    (fun A : Subgroup H => A.map (MulAut.conj a⁻¹).toMonoidHom)
    (ha.symm.trans hb)
  rw [coherent_conjugate_twice, coherent_conjugate_twice, inv_mul_cancel] at h
  have hone : (J (σ p)).map (MulAut.conj (1 : H)).toMonoidHom = J (σ p) := by
    rw [map_one]
    exact Subgroup.map_id _
  rw [hone] at h
  exact hsep (σ p) (τ p) (a⁻¹ * b) h

/-- Fixed-label export usable for the SAME lifted τ chosen on the actual
matched square covers. The only supplied facts are its arithmetic inclusion
square and actual inertia conjugacies, already retained by the construction. -/
theorem bare_rationalConfiguration_crossRatio_cyclic_classes_fixed_inertia
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
      eP (rationalConfigurationGeometricInclusion k κ s Ω₁ v))
    (σ : s ≃ t)
    (hI : ∀ p : s, ∃ a : rationalConfigurationGeometricGroup k κ t Ω₂,
      (rationalConfigurationChosenInertia k κ s Ω₁
        (rationalConfigurationBoundaryPlace k κ s p)).map eΔ.toMonoidHom =
      (rationalConfigurationChosenInertia k κ t Ω₂
        (rationalConfigurationBoundaryPlace k κ t (σ p))).map
          (MulAut.conj a).toMonoidHom) :
        ∀ (a b c₀ c : s), a ≠ b →
      c₀ ≠ a → c₀ ≠ b → c ≠ a → c ≠ b →
      ∃ A B : kˣ,
        (A : k) = crossRatio a.val b.val c₀.val c.val ∧
        (B : k) = crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val ∧
        Subgroup.zpowers A = Subgroup.zpowers B := by
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
  have hlabels : τ = σ := by
    apply inertiaLabelEquiv_unique eΔ.toMulEquiv
      (fun p : s => rationalConfigurationChosenInertia k κ s Ω₁
        (rationalConfigurationBoundaryPlace k κ s p))
      (fun p : t => rationalConfigurationChosenInertia k κ t Ω₂
        (rationalConfigurationBoundaryPlace k κ t p)) τ σ hτ hI
    intro p q a hpq
    apply (rationalConfigurationBoundaryPlaceEquiv k κ t).injective
    exact rationalConfigurationChosenInertia_eq_conjugate_imp_eq
      k κ t ht Ω₂
      (rationalConfigurationBoundaryPlace k κ t p)
      (rationalConfigurationBoundaryPlace k κ t q) a hpq
  subst τ
  exact hclasses

end AnabelianGeometry.WeightFiltration
