/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.AdicPullback
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Actual adic H¹ as the image of geometric pullback

A surjection on the original fundamental groups makes rational H¹ pullback
injective. The resulting equivalence onto its literal image retains the
original pullback map. It can be used, in particular, for normal
compactifications without adding a cohomological injectivity hypothesis.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleCohomology.Classical

namespace EtaleFundamentalGroups.Cohomology

universe u

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
  (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ξ : Spec (.of Ω) ⟶ X) (ℓ : ℕ) [Fact ℓ.Prime]

/-- Surjectivity on actual fundamental groups implies injectivity on rational H¹. -/
theorem rationalEllAdicH1Pullback_injective
    (hf : Function.Surjective (FiniteEtale.fundamentalGroupHom f ξ)) :
    Function.Injective (rationalEllAdicPullback f ℓ 1) := by
  intro a b hab
  apply (rationalEllAdicH1CharacterEquiv (ξ ≫ f) ℓ).injective
  apply ContinuousMonoidHom.ext
  intro g
  obtain ⟨h, rfl⟩ := hf g
  have hn (c : rationalEllAdicCohomology ℓ Y 1) :=
    congrArg (fun χ : rationalPadicCharacters ξ ℓ => χ.toMul h)
      (LinearMap.congr_fun (rationalEllAdicH1Character_schemePullback f ξ ℓ) c)
  exact (hn a).symm.trans ((congrArg
    (fun c => (rationalEllAdicH1CharacterEquiv ξ ℓ c).toMul h) hab).trans (hn b))

/-- The domain of rational H¹ pullback is canonically its literal image. -/
def rationalEllAdicH1PullbackImageEquiv
    (hf : Function.Surjective (FiniteEtale.fundamentalGroupHom f ξ)) :
    rationalEllAdicCohomology ℓ Y 1 ≃ₗ[ℚ_[ℓ]]
      LinearMap.range (rationalEllAdicPullback f ℓ 1) :=
  LinearEquiv.ofInjective (rationalEllAdicPullback f ℓ 1)
    (rationalEllAdicH1Pullback_injective f ξ ℓ hf)

/-- The image equivalence is exactly the original geometric pullback. -/
@[simp] theorem rationalEllAdicH1PullbackImageEquiv_apply
    (hf : Function.Surjective (FiniteEtale.fundamentalGroupHom f ξ))
    (a : rationalEllAdicCohomology ℓ Y 1) :
    (rationalEllAdicH1PullbackImageEquiv f ξ ℓ hf a :
      rationalEllAdicCohomology ℓ X 1) = rationalEllAdicPullback f ℓ 1 a := rfl

end EtaleFundamentalGroups.Cohomology
