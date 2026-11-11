/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Frobenius.Adic
public import Nyll.EtaleFundamentalGroups.Cohomology.H1CharacterPullback
public import Nyll.EtaleFundamentalGroups.Cohomology.RationalH1Comparison

/-!
# Geometric naturality of actual integral and rational ℓ-adic H¹

Finite-coefficient geometric naturality passes to the actual inverse limit and
its rationalization. The group homomorphism is the existing map on étale
fundamental groups induced by the original scheme morphism. In particular,
applying this to the scheme Frobenius computes its actual rational H¹ action.

This comparison is characteristic-free. It does not identify the fundamental
group of a compactification with a weight quotient of an affine mixed quotient.

-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory EtaleCohomology.Classical
open scoped TensorProduct

namespace EtaleFundamentalGroups.Cohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X)
  (ℓ : ℕ) [Fact ℓ.Prime]

/-- Precomposition by the actual fundamental-group map on integral characters. -/
def padicCharacterSchemePullback :
    padicCharacters (ξ ≫ f) ℓ →ₗ[ℤ_[ℓ]] padicCharacters ξ ℓ where
  toFun χ := Additive.ofMul (χ.toMul.comp (FiniteEtale.fundamentalGroupHom f ξ))
  map_add' _ _ := ContinuousMonoidHom.ext fun _ => rfl
  map_smul' _ _ := ContinuousMonoidHom.ext fun _ => rfl

/-- Precomposition by the actual fundamental-group map on rational characters. -/
def rationalCharacterSchemePullback :
    rationalPadicCharacters (ξ ≫ f) ℓ →ₗ[ℚ_[ℓ]] rationalPadicCharacters ξ ℓ where
  toFun χ := Additive.ofMul (χ.toMul.comp (FiniteEtale.fundamentalGroupHom f ξ))
  map_add' _ _ := ContinuousMonoidHom.ext fun _ => rfl
  map_smul' _ _ := ContinuousMonoidHom.ext fun _ => rfl

variable [ConnectedSpace X] [ConnectedSpace Y] [IsSepClosed Ω]

attribute [local instance] finiteCoefficientTopology finiteCoefficientDiscrete

/-- Integral H¹ pullback is precomposition by the actual fundamental-group map. -/
theorem ellAdicH1Character_schemePullback (a : ellAdicCohomology Y ℓ 1) :
    ellAdicH1PadicCharacterLinearEquiv ξ ℓ (ellAdicPullback f ℓ 1 a) =
      padicCharacterSchemePullback f ξ ℓ
        (ellAdicH1PadicCharacterLinearEquiv (ξ ≫ f) ℓ a) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  apply ContinuousMonoidHom.ext
  intro g
  have hv :
      ((ellAdicH1PadicCharacterEquiv ξ ℓ (ellAdicPullback f ℓ 1 a)).toMul g).toAdd =
        ((ellAdicH1PadicCharacterEquiv (ξ ≫ f) ℓ a).toMul
          (FiniteEtale.fundamentalGroupHom f ξ g)).toAdd := by
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
        have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero ℓ)
        exact Subsingleton.elim _ _
    | succ n =>
        rw [ellAdicH1PadicCharacterEquiv_reduction,
          ellAdicH1PadicCharacterEquiv_reduction]
        exact (congrArg (fun χ : Aut (FiniteEtale.fiber ξ) →ₜ*
          Multiplicative (ellPowerCoefficients ℓ n) => (χ g).toAdd.down)
            (h1Character_schemePullback f (ellPowerCoefficients ℓ n) ξ (a.val n))).symm
  exact congrArg Multiplicative.ofAdd hv

private theorem rationalComparison_tmul
    (c : ℚ_[ℓ]) (a : ellAdicCohomology X ℓ 1) :
    rationalEllAdicH1CharacterEquiv ξ ℓ (c ⊗ₜ[ℤ_[ℓ]] a) =
      c • integralCharacterInclusion ξ ℓ (ellAdicH1PadicCharacterLinearEquiv ξ ℓ a) := by
  change rationalCharacterTensorEquiv ξ ℓ
      (c ⊗ₜ[ℤ_[ℓ]] ellAdicH1PadicCharacterLinearEquiv ξ ℓ a) = _
  exact rationalCharacterTensorEquiv_tmul ξ ℓ c
    (ellAdicH1PadicCharacterLinearEquiv ξ ℓ a)

/-- Rational H¹ naturality as equality of linear maps on actual cohomology. -/
theorem rationalEllAdicH1Character_schemePullback :
    (rationalEllAdicH1CharacterEquiv ξ ℓ).toLinearMap.comp
        (rationalEllAdicPullback f ℓ 1) =
      (rationalCharacterSchemePullback f ξ ℓ).comp
        (rationalEllAdicH1CharacterEquiv (ξ ≫ f) ℓ).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c a
  change rationalEllAdicH1CharacterEquiv ξ ℓ
      ((ellAdicPullback f ℓ 1).baseChange ℚ_[ℓ] (c ⊗ₜ[ℤ_[ℓ]] a)) =
    rationalCharacterSchemePullback f ξ ℓ
      (rationalEllAdicH1CharacterEquiv (ξ ≫ f) ℓ (c ⊗ₜ[ℤ_[ℓ]] a))
  rw [LinearMap.baseChange_tmul, rationalComparison_tmul,
    rationalComparison_tmul, map_smul]
  apply congrArg (c • ·)
  have hi (χ : padicCharacters (ξ ≫ f) ℓ) :
      rationalCharacterSchemePullback f ξ ℓ (integralCharacterInclusion (ξ ≫ f) ℓ χ) =
        integralCharacterInclusion ξ ℓ (padicCharacterSchemePullback f ξ ℓ χ) := rfl
  rw [hi, ← ellAdicH1Character_schemePullback]

end EtaleFundamentalGroups.Cohomology
