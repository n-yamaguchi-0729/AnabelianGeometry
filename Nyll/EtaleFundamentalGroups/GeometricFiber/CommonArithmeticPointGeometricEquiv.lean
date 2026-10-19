/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.GeometricAbelianGaloisAction
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticExactSequence

/-! # Comparison of geometric fibers through a common arithmetic point -/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable
    (k κ : Type u) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]

private theorem geometricKernelEquiv_commonPoint_apply
    (x : Spec (.of Ω) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)
    (z : Spec (.of Ω) ⟶ X) (h : x ≫ Limits.pullback.snd _ f = z)
    (g : π₁ᵉᵗ(x)) :
    let E : π₁ᵉᵗ(x) ≃ₜ* (arithmeticFundamentalGroupHom k κ f z).toMonoidHom.ker :=
      h ▸ geometricFundamentalGroupKernelEquiv k κ X f x
    (E g : π₁ᵉᵗ(z)) =
      pointedFundamentalGroupHom (Limits.pullback.snd _ f) x z h g := by
  subst z
  exact geometricFundamentalGroupKernelEquiv_apply k κ X f x g

theorem commonArithmeticPoint_projection_exact
    (x : Spec (.of Ω) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)
    (z : Spec (.of Ω) ⟶ X) (h : x ≫ Limits.pullback.snd _ f = z) :
    Function.Injective (pointedFundamentalGroupHom (Limits.pullback.snd _ f) x z h) ∧
      (pointedFundamentalGroupHom (Limits.pullback.snd _ f) x z h).toMonoidHom.range =
        (arithmeticFundamentalGroupHom k κ f z).toMonoidHom.ker := by
  subst z
  have hex := arithmetic_exactSequence_of_isSepClosure k κ X f x
  exact ⟨hex.1, hex.2.2.symm⟩

variable
    (x₀ x₁ : Spec (.of Ω) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)
    (z : Spec (.of Ω) ⟶ X)
    (h₀ : x₀ ≫ Limits.pullback.snd _ f = z)
    (h₁ : x₁ ≫ Limits.pullback.snd _ f = z)

/-- Identify geometric fundamental groups over the same arithmetic point through their
identifications with the kernel of the arithmetic fundamental group homomorphism. -/
def commonArithmeticPointGeometricEquiv : π₁ᵉᵗ(x₀) ≃ₜ* π₁ᵉᵗ(x₁) :=
  let E₀ : π₁ᵉᵗ(x₀) ≃ₜ* (arithmeticFundamentalGroupHom k κ f z).toMonoidHom.ker :=
    h₀ ▸ geometricFundamentalGroupKernelEquiv k κ X f x₀
  let E₁ : π₁ᵉᵗ(x₁) ≃ₜ* (arithmeticFundamentalGroupHom k κ f z).toMonoidHom.ker :=
    h₁ ▸ geometricFundamentalGroupKernelEquiv k κ X f x₁
  E₀.trans E₁.symm

theorem commonArithmeticPointGeometricEquiv_projection (g : π₁ᵉᵗ(x₀)) :
    pointedFundamentalGroupHom (Limits.pullback.snd _ f) x₁ z h₁
      (commonArithmeticPointGeometricEquiv k κ X f x₀ x₁ z h₀ h₁ g) =
    pointedFundamentalGroupHom (Limits.pullback.snd _ f) x₀ z h₀ g := by
  let E₀ : π₁ᵉᵗ(x₀) ≃ₜ* (arithmeticFundamentalGroupHom k κ f z).toMonoidHom.ker :=
    h₀ ▸ geometricFundamentalGroupKernelEquiv k κ X f x₀
  let E₁ : π₁ᵉᵗ(x₁) ≃ₜ* (arithmeticFundamentalGroupHom k κ f z).toMonoidHom.ker :=
    h₁ ▸ geometricFundamentalGroupKernelEquiv k κ X f x₁
  change pointedFundamentalGroupHom (Limits.pullback.snd _ f) x₁ z h₁
      (E₁.symm (E₀ g)) =
    pointedFundamentalGroupHom (Limits.pullback.snd _ f) x₀ z h₀ g
  calc
    pointedFundamentalGroupHom (Limits.pullback.snd _ f) x₁ z h₁
        (E₁.symm (E₀ g)) = (E₁ (E₁.symm (E₀ g)) : π₁ᵉᵗ(z)) :=
      (geometricKernelEquiv_commonPoint_apply k κ X f x₁ z h₁ (E₁.symm (E₀ g))).symm
    _ = (E₀ g : π₁ᵉᵗ(z)) :=
      congrArg Subtype.val (E₁.apply_symm_apply (E₀ g))
    _ = pointedFundamentalGroupHom (Limits.pullback.snd _ f) x₀ z h₀ g :=
      geometricKernelEquiv_commonPoint_apply k κ X f x₀ z h₀ g

theorem commonArithmeticPointGeometricEquiv_unique
    (e : π₁ᵉᵗ(x₀) ≃ₜ* π₁ᵉᵗ(x₁))
    (he : ∀ g, pointedFundamentalGroupHom (Limits.pullback.snd _ f) x₁ z h₁ (e g) =
      pointedFundamentalGroupHom (Limits.pullback.snd _ f) x₀ z h₀ g) :
    e = commonArithmeticPointGeometricEquiv k κ X f x₀ x₁ z h₀ h₁ := by
  let E₁ : π₁ᵉᵗ(x₁) ≃ₜ* (arithmeticFundamentalGroupHom k κ f z).toMonoidHom.ker :=
    h₁ ▸ geometricFundamentalGroupKernelEquiv k κ X f x₁
  apply ContinuousMulEquiv.ext
  intro g
  apply E₁.injective
  apply Subtype.ext
  calc
    (E₁ (e g) : π₁ᵉᵗ(z)) =
        pointedFundamentalGroupHom (Limits.pullback.snd _ f) x₁ z h₁ (e g) :=
      geometricKernelEquiv_commonPoint_apply k κ X f x₁ z h₁ (e g)
    _ = pointedFundamentalGroupHom (Limits.pullback.snd _ f) x₀ z h₀ g := he g
    _ = pointedFundamentalGroupHom (Limits.pullback.snd _ f) x₁ z h₁
        (commonArithmeticPointGeometricEquiv k κ X f x₀ x₁ z h₀ h₁ g) :=
      (commonArithmeticPointGeometricEquiv_projection k κ X f x₀ x₁ z h₀ h₁ g).symm
    _ = (E₁ (commonArithmeticPointGeometricEquiv k κ X f x₀ x₁ z h₀ h₁ g) : π₁ᵉᵗ(z)) :=
      (geometricKernelEquiv_commonPoint_apply k κ X f x₁ z h₁
        (commonArithmeticPointGeometricEquiv k κ X f x₀ x₁ z h₀ h₁ g)).symm

end AlgebraicGeometry.FiniteEtale
