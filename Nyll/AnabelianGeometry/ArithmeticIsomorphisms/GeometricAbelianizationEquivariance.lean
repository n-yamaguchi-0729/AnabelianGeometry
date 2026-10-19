/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticKernelEquivalence
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps

/-! # Equivariance of a specified geometric comparison

The arithmetic square determines the geometric comparison uniquely. Thus the
same comparison, with its existing boundary labels, has Galois-equivariant
abelianization, even when the arithmetic basepoints are specified separately.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale ProCGroups.Abelian

namespace AnabelianGeometry.ArithmeticIsomorphisms

/-- The given geometric equivalence, not a newly chosen one, has equivariant
abelianization whenever its actual pointed arithmetic square commutes. -/
theorem geometricAbelianization_equivariant_of_pointed_arithmetic_square
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    (X₁ X₂ : Scheme)
    [CompactSpace X₁] [QuasiSeparatedSpace X₁]
    [CompactSpace X₂] [QuasiSeparatedSpace X₂]
    (f₁ : X₁ ⟶ Spec (.of k)) (f₂ : X₂ ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f₁)]
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f₂)]
    {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (xi₁ : Spec (.of Ω₁) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f₁)
    (xi₂ : Spec (.of Ω₂) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f₂)
    (x₁ : Spec (.of Ω₁) ⟶ X₁) (x₂ : Spec (.of Ω₂) ⟶ X₂)
    (hx₁ : xi₁ ≫ Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f₁ = x₁)
    (hx₂ : xi₂ ≫ Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f₂ = x₂)
    (eP : π₁ᵉᵗ(x₁) ≃ₜ* π₁ᵉᵗ(x₂))
    (hP : ∀ v, arithmeticFundamentalGroupHom k κ f₂ x₂ (eP v) =
      arithmeticFundamentalGroupHom k κ f₁ x₁ v)
    (eG : π₁ᵉᵗ(xi₁) ≃ₜ* π₁ᵉᵗ(xi₂))
    (hG : ∀ v,
      pointedFundamentalGroupHom (Limits.pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f₂) xi₂ x₂ hx₂ (eG v) =
        eP (pointedFundamentalGroupHom (Limits.pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f₁) xi₁ x₁ hx₁ v)) :
    ∀ (σ : κ ≃ₐ[k] κ) (v : TopologicalAbelianization (π₁ᵉᵗ(xi₁))),
      TopologicalAbelianization.congr eG (geometricAbelianGaloisAction k κ X₁ f₁ xi₁ σ v) =
        geometricAbelianGaloisAction k κ X₂ f₂ xi₂ σ
          (TopologicalAbelianization.congr eG v) := by
  subst x₁
  subst x₂
  obtain ⟨e, he, hequiv⟩ := exists_geometricEquiv_equivariant_of_arithmeticEquiv
    k κ X₁ X₂ f₁ f₂ xi₁ xi₂ eP hP
  have hsame : eG = e := by
    apply ContinuousMulEquiv.ext
    intro v
    apply (arithmetic_exactSequence_of_isSepClosure k κ X₂ f₂ xi₂).1
    exact (hG v).trans (he v).symm
  rw [hsame]
  exact hequiv

end AnabelianGeometry.ArithmeticIsomorphisms
