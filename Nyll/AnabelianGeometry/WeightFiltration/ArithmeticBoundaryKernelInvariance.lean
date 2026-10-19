/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.LiteralArithmeticBoundaryWeight
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticKernelEquivalence

/-! # Boundary weight preserved by the original arithmetic isomorphism

The compactifications have actual rational sections. No preservation of their
boundary kernels, boundary points or inertia groups is assumed. The intrinsic
cyclotomic-span theorem supplies the kernel comparison from Galois equivariance.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory AlgebraicGeometry.FiniteEtale
open AlgebraicGeometry.SmoothProperCurve EtaleFundamentalGroups
open EtaleFundamentalGroups.Inertia ProCGroups.Abelian NeronModelInfra

namespace AnabelianGeometry.WeightFiltration

/-- An arithmetic isomorphism over the same number field preserves the actual
compactification kernel on geometric abelianization. The rational sections
belong to the compactifications and need not lie in the open curves. -/
theorem arithmeticEquiv_preserves_compactification_abelian_kernel
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsSepClosure k κ]
    {C₁ C₂ U₁ U₂ : Scheme}
    [CompactSpace U₁] [QuasiSeparatedSpace U₁]
    [CompactSpace U₂] [QuasiSeparatedSpace U₂]
    (c₁ : C₁ ⟶ Spec (.of k)) (c₂ : C₂ ⟶ Spec (.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : U₁ ⟶ C₁) (i₂ : U₂ ⟶ C₂) [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [IsIntegral (Limits.pullback (specMap k κ) (i₁ ≫ c₁))]
    [IsIntegral (Limits.pullback (specMap k κ) (i₂ ≫ c₂))]
    {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    [Algebra (Limits.pullback (specMap k κ) (i₁ ≫ c₁)).functionField Ω₁]
    [Algebra (Limits.pullback (specMap k κ) (i₂ ≫ c₂)).functionField Ω₂]
    [IsSepClosure (Limits.pullback (specMap k κ) (i₁ ≫ c₁)).functionField Ω₁]
    [IsSepClosure (Limits.pullback (specMap k κ) (i₂ ≫ c₂)).functionField Ω₂]
    (ε₁ : SchemeHomOver (𝟙 (Spec (.of k))) c₁)
    (ε₂ : SchemeHomOver (𝟙 (Spec (.of k))) c₂)
    (eP : Aut (fiber
        ((Limits.pullback (specMap k κ) (i₁ ≫ c₁)).genericExtensionMorphism Ω₁ ≫
          Limits.pullback.snd (specMap k κ) (i₁ ≫ c₁))) ≃ₜ*
      Aut (fiber
        ((Limits.pullback (specMap k κ) (i₂ ≫ c₂)).genericExtensionMorphism Ω₂ ≫
          Limits.pullback.snd (specMap k κ) (i₂ ≫ c₂))))
    (hP : ∀ γ, arithmeticFundamentalGroupHom k κ (i₂ ≫ c₂)
        ((Limits.pullback (specMap k κ) (i₂ ≫ c₂)).genericExtensionMorphism Ω₂ ≫
          Limits.pullback.snd (specMap k κ) (i₂ ≫ c₂)) (eP γ) =
      arithmeticFundamentalGroupHom k κ (i₁ ≫ c₁)
        ((Limits.pullback (specMap k κ) (i₁ ≫ c₁)).genericExtensionMorphism Ω₁ ≫
          Limits.pullback.snd (specMap k κ) (i₁ ≫ c₁)) γ) :
    let x₁ := (Limits.pullback (specMap k κ) (i₁ ≫ c₁)).genericExtensionMorphism Ω₁
    let x₂ := (Limits.pullback (specMap k κ) (i₂ ≫ c₂)).genericExtensionMorphism Ω₂
    ∃ eΔ : Aut (fiber x₁) ≃ₜ* Aut (fiber x₂),
      (∀ v, fundamentalGroupHom (Limits.pullback.snd (specMap k κ) (i₂ ≫ c₂)) x₂ (eΔ v) =
        eP (fundamentalGroupHom (Limits.pullback.snd (specMap k κ) (i₁ ≫ c₁)) x₁ v)) ∧
      ((compactificationAbelianizationMap (coefficientModelMap (specMap k κ) c₁ i₁)
        x₁).toMonoidHom.ker).map
          (TopologicalAbelianization.congr eΔ).toMulEquiv.toMonoidHom =
        (compactificationAbelianizationMap (coefficientModelMap (specMap k κ) c₂ i₂)
          x₂).toMonoidHom.ker := by
  intro x₁ x₂
  obtain ⟨eΔ, hΔ, hAb⟩ := exists_geometricEquiv_equivariant_of_arithmeticEquiv
    k κ U₁ U₂ (i₁ ≫ c₁) (i₂ ≫ c₂) x₁ x₂ eP hP
  refine ⟨eΔ, hΔ, ?_⟩
  rw [literalArithmetic_compactification_kernel_eq_openCyclotomicSpan
    k κ c₁ i₁ ε₁,
    literalArithmetic_compactification_kernel_eq_openCyclotomicSpan
      k κ c₂ i₂ ε₂]
  exact openCyclotomicSpan_map_equiv
    (fun σ : κ ≃ₐ[k] κ => primeToRootsCoefficientMap κ κ σ.toRingHom)
    (fun σ => geometricAbelianGaloisAction k κ U₁ (i₁ ≫ c₁) x₁ σ)
    (fun σ => geometricAbelianGaloisAction k κ U₂ (i₂ ≫ c₂) x₂ σ)
    (TopologicalAbelianization.congr eΔ).toMulEquiv hAb

end AnabelianGeometry.WeightFiltration
