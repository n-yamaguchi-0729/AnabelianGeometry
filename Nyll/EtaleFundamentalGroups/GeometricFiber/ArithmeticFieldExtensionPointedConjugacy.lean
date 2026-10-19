/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticFieldExtensionConjugacy
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps

/-! # The actual finite-base arithmetic label at the prescribed target point -/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Equality transport of the original target point preserves the actual
field-extension comparison and its single uniform conjugator. -/
theorem arithmeticFundamentalGroupHom_fieldExtension_pointed_conjugate
    (k E κ : Type u) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosure E κ]
    {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (c : Y ⟶ Spec (.of E)) (a : Y ⟶ X)
    (ha : a ≫ f = c ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xiY : Spec (.of Ω) ⟶ Y) (xiX : Spec (.of Ω) ⟶ X)
    (hpoint : xiY ≫ a = xiX) :
    ∃ α : Gal(κ/k), ∀ γ : π₁ᵉᵗ(xiY),
      (arithmeticFundamentalGroupHom E κ c xiY γ).restrictScalars k =
        α * arithmeticFundamentalGroupHom k κ f xiX
          (pointedFundamentalGroupHom a xiY xiX hpoint γ) * α⁻¹ := by
  subst xiX
  exact arithmeticFundamentalGroupHom_fieldExtension_conjugate k E κ f c a ha xiY

end AlgebraicGeometry.FiniteEtale
