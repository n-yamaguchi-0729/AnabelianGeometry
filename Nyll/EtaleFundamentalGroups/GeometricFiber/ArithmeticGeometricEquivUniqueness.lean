/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticKernelEquivalence

/-! # Uniqueness of the actual geometric equivalence above an arithmetic equivalence

The original geometric inclusions are injective by the arithmetic exact sequence.
Thus recognition of different source cusps cannot change the geometric equivalence
lying above the fixed arithmetic map.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Two actual geometric equivalences above the same arithmetic equivalence agree. -/
theorem geometricEquiv_eq_of_same_arithmeticEquiv
    (k κ : Type u) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    (X₁ X₂ : Scheme.{u})
    [CompactSpace X₁] [QuasiSeparatedSpace X₁]
    [CompactSpace X₂] [QuasiSeparatedSpace X₂]
    (f₁ : X₁ ⟶ Spec (.of k)) (f₂ : X₂ ⟶ Spec (.of k))
    [ConnectedSpace (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f₂ : Scheme)]
    {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (xi₁ : Spec (.of Ω₁) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f₁)
    (xi₂ : Spec (.of Ω₂) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f₂)
    (eP : Aut (fiber (xi₁ ≫ Limits.pullback.snd _ f₁)) ≃ₜ*
      Aut (fiber (xi₂ ≫ Limits.pullback.snd _ f₂)))
    (eΔ eΔ' : Aut (fiber xi₁) ≃ₜ* Aut (fiber xi₂))
    (hΔ : ∀ v, fundamentalGroupHom (Limits.pullback.snd _ f₂) xi₂ (eΔ v) =
      eP (fundamentalGroupHom (Limits.pullback.snd _ f₁) xi₁ v))
    (hΔ' : ∀ v, fundamentalGroupHom (Limits.pullback.snd _ f₂) xi₂ (eΔ' v) =
      eP (fundamentalGroupHom (Limits.pullback.snd _ f₁) xi₁ v)) :
    eΔ = eΔ' := by
  apply ContinuousMulEquiv.ext
  intro v
  exact (arithmetic_exactSequence_of_isSepClosure k κ X₂ f₂ xi₂).1
    ((hΔ v).trans (hΔ' v).symm)

end AlgebraicGeometry.FiniteEtale
