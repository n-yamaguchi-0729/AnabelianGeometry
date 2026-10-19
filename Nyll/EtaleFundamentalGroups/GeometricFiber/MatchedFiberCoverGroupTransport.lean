/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.PointedCoverGroupTransport

/-! # The same finite-fibre map selects the actual two covering base points

The source point is retained, and the target point is its image under the
already given fibre equivalence. The point-matching premise of the stabilizer
transport theorem is consequently proved from the original fibre/point
comparison, rather than postulated as a label-preservation hypothesis.
-/
noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The actual field-valued lift represented by the original fibre point. -/
def actualFiberPointLift (xi : Spec (.of Ω) ⟶ S) (A : FiniteEtale S)
    (w : (fiber xi).obj A) : Spec (.of Ω) ⟶ A.left :=
  (fiberObjEquivHom xi A w).left

/-- This is a lift of the original geometric base point. -/
theorem actualFiberPointLift_comp (xi : Spec (.of Ω) ⟶ S) (A : FiniteEtale S)
    (w : (fiber xi).obj A) : actualFiberPointLift xi A w ≫ A.hom = xi :=
  (fiberObjEquivHom xi A w).w

/-- Re-reading this literal lift gives exactly the original fibre point. -/
theorem actualFiberPointLift_fiberPoint (xi : Spec (.of Ω) ⟶ S) (A : FiniteEtale S)
    (w : (fiber xi).obj A) :
    (fiberObjEquivHom xi A).symm
      (Over.homMk (actualFiberPointLift xi A w) (actualFiberPointLift_comp xi A w)) = w := by
  apply (fiberObjEquivHom xi A).injective
  rw [Equiv.apply_symm_apply]
  apply Over.OverMorphism.ext
  rfl

variable {T : Scheme.{u}} [ConnectedSpace S] [ConnectedSpace T]
variable {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
variable (AS : FiniteEtale S) (AT : FiniteEtale T)
variable (ξs : Spec (.of Ω₁) ⟶ S) (ξt : Spec (.of Ω₂) ⟶ T)
variable (α : π₁ᵉᵗ(ξs) ≃ₜ* π₁ᵉᵗ(ξt))
variable (e : (fiber ξs).obj AS ≃ (fiber ξt).obj AT)
variable (he : ∀ g x, e (g • x) = α g • e x)
variable (w : (fiber ξs).obj AS)

/-- Restrict the original base-group equivalence to the covering groups at
the source point and its image under the same fibre equivalence. -/
def matchedFiberCoverGroupTransport :
    π₁ᵉᵗ(actualFiberPointLift ξs AS w) ≃ₜ*
      π₁ᵉᵗ(actualFiberPointLift ξt AT (e w)) :=
  pointedCoverGroupTransport AS AT ξs ξt
    (actualFiberPointLift ξs AS w) (actualFiberPointLift ξt AT (e w))
    (actualFiberPointLift_comp ξs AS w) (actualFiberPointLift_comp ξt AT (e w))
    α e he (by rw [actualFiberPointLift_fiberPoint, actualFiberPointLift_fiberPoint])

/-- Its actual cover inclusion square retains α pointwise. -/
theorem matchedFiberCoverGroupTransport_inclusion
    (g : π₁ᵉᵗ(actualFiberPointLift ξs AS w)) :
    pointedFundamentalGroupHom AT.hom (actualFiberPointLift ξt AT (e w)) ξt
      (actualFiberPointLift_comp ξt AT (e w))
      (matchedFiberCoverGroupTransport AS AT ξs ξt α e he w g) =
        α (pointedFundamentalGroupHom AS.hom (actualFiberPointLift ξs AS w) ξs
          (actualFiberPointLift_comp ξs AS w) g) :=
  pointedCoverGroupTransport_inclusion AS AT ξs ξt
    (actualFiberPointLift ξs AS w) (actualFiberPointLift ξt AT (e w))
    (actualFiberPointLift_comp ξs AS w) (actualFiberPointLift_comp ξt AT (e w))
    α e he (by rw [actualFiberPointLift_fiberPoint, actualFiberPointLift_fiberPoint]) g

/-- The same arithmetic quotient equality restricts to these actual matched
cover groups. No independently matched covering base points are assumed. -/
theorem matchedFiberCoverGroupTransport_quotient
    {Γ : Type*} [Monoid Γ] (qs : π₁ᵉᵗ(ξs) →* Γ) (qt : π₁ᵉᵗ(ξt) →* Γ)
    (hq : ∀ a, qt (α a) = qs a)
    (g : π₁ᵉᵗ(actualFiberPointLift ξs AS w)) :
    qt (pointedFundamentalGroupHom AT.hom (actualFiberPointLift ξt AT (e w)) ξt
      (actualFiberPointLift_comp ξt AT (e w))
      (matchedFiberCoverGroupTransport AS AT ξs ξt α e he w g)) =
        qs (pointedFundamentalGroupHom AS.hom (actualFiberPointLift ξs AS w) ξs
          (actualFiberPointLift_comp ξs AS w) g) := by
  rw [matchedFiberCoverGroupTransport_inclusion]
  exact hq _

end AlgebraicGeometry.FiniteEtale
