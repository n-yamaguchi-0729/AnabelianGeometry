/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.MatchedFiberCoverGroupTransport
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticNaturality

/-! # Intrinsic arithmetic compatibility on the same actual pointed covers

The actual arithmetic map is functorial for a morphism over the same constant
field. Consequently the exact matched-fibre covering-group transport preserves
the covers' own arithmetic maps, not merely unnamed quotient homomorphisms.
-/
noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Specifying the original target point keeps arithmetic naturality literal. -/
theorem arithmeticFundamentalGroupHom_pointed_comp
    (k κ : Type u) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    {X Y : Scheme.{u}} (j : X ⟶ Y) (f : Y ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y) (h : x ≫ j = y)
    (g : π₁ᵉᵗ(x)) :
    arithmeticFundamentalGroupHom k κ f y (pointedFundamentalGroupHom j x y h g) =
      arithmeticFundamentalGroupHom k κ (j ≫ f) x g := by
  subst y
  exact arithmeticFundamentalGroupHom_comp k κ j f x g

/-- The covering-group equivalence selected by the unchanged finite-fibre
map commutes with the intrinsic arithmetic maps of the actual two covers. -/
theorem matchedFiberCoverGroupTransport_arithmetic
    (k κ : Type u) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    {S T : Scheme.{u}} [ConnectedSpace S] [ConnectedSpace T]
    {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (AS : FiniteEtale S) (AT : FiniteEtale T)
    (fs : S ⟶ Spec (.of k)) (ft : T ⟶ Spec (.of k))
    (ξs : Spec (.of Ω₁) ⟶ S) (ξt : Spec (.of Ω₂) ⟶ T)
    (α : π₁ᵉᵗ(ξs) ≃ₜ* π₁ᵉᵗ(ξt))
    (hα : ∀ a, arithmeticFundamentalGroupHom k κ ft ξt (α a) =
      arithmeticFundamentalGroupHom k κ fs ξs a)
    (e : (fiber ξs).obj AS ≃ (fiber ξt).obj AT)
    (he : ∀ g x, e (g • x) = α g • e x)
    (w : (fiber ξs).obj AS) (g : π₁ᵉᵗ(actualFiberPointLift ξs AS w)) :
    arithmeticFundamentalGroupHom k κ (AT.hom ≫ ft)
      (actualFiberPointLift ξt AT (e w))
      (matchedFiberCoverGroupTransport AS AT ξs ξt α e he w g) =
        arithmeticFundamentalGroupHom k κ (AS.hom ≫ fs)
          (actualFiberPointLift ξs AS w) g := by
  rw [← arithmeticFundamentalGroupHom_pointed_comp k κ AT.hom ft
    (actualFiberPointLift ξt AT (e w)) ξt (actualFiberPointLift_comp ξt AT (e w))]
  rw [matchedFiberCoverGroupTransport_inclusion, hα]
  exact arithmeticFundamentalGroupHom_pointed_comp k κ AS.hom fs
    (actualFiberPointLift ξs AS w) ξs (actualFiberPointLift_comp ξs AS w) g

end AlgebraicGeometry.FiniteEtale
