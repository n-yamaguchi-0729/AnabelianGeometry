/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.PointedCoverImage
import Nyll.EtaleFundamentalGroups.GeometricFiber.PointedCoverInjectivity

/-! # Actual pointed-cover group transport from the same finite-fibre map

An equivariant equivalence of the original cover fibres restricts the original
base-group equivalence to the corresponding actual lifted-point stabilizers.
The pointed-cover stabilizer comparison then gives a topological
isomorphism of the actual covering fundamental groups. Its inclusion square is
literal, so every original compatible arithmetic quotient remains compatible.
-/
noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace MulAction

/-- Restrict the same group and fibre equivalences to the actual stabilizers
of two points already matched by the fibre equivalence. -/
def stabilizerContinuousMulEquivOfEquivariant
    {G H X Y : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [MulAction G X] [MulAction H Y]
    (α : G ≃ₜ* H) (e : X ≃ Y)
    (he : ∀ g x, e (g • x) = α g • e x)
    (x : X) (y : Y) (hxy : e x = y) : stabilizer G x ≃ₜ* stabilizer H y where
  toFun g := ⟨α g.val, by
    change α g.val • y = y
    rw [← hxy, ← he]
    exact congrArg e g.property⟩
  invFun h := ⟨α.symm h.val, by
    change α.symm h.val • x = x
    apply e.injective
    rw [he, α.apply_symm_apply, hxy]
    exact h.property⟩
  left_inv g := Subtype.ext (α.symm_apply_apply g.val)
  right_inv h := Subtype.ext (α.apply_symm_apply h.val)
  map_mul' g h := Subtype.ext (α.map_mul g.val h.val)
  continuous_toFun := (α.continuous_toFun.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (α.symm.continuous_toFun.comp continuous_subtype_val).subtype_mk _

@[simp] theorem stabilizerContinuousMulEquivOfEquivariant_coe
    {G H X Y : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [MulAction G X] [MulAction H Y]
    (α : G ≃ₜ* H) (e : X ≃ Y)
    (he : ∀ g x, e (g • x) = α g • e x)
    (x : X) (y : Y) (hxy : e x = y) (g : stabilizer G x) :
    (stabilizerContinuousMulEquivOfEquivariant α e he x y hxy g : H) = α g := rfl

end MulAction

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- The stabilizer equivalence, with the actual chosen base point
and its literal lifted fibre point displayed without a transported subgroup. -/
def pointedCoverGroupEquivStabilizer
    {S : Scheme.{u}} [ConnectedSpace S]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (A : FiniteEtale S) (x : Spec (.of Ω) ⟶ A.left)
    (xi : Spec (.of Ω) ⟶ S) (h : x ≫ A.hom = xi) :
    π₁ᵉᵗ(x) ≃ₜ* MulAction.stabilizer π₁ᵉᵗ(xi)
      ((fiberObjEquivHom xi A).symm (Over.homMk x h)) := by
  subst xi
  exact fundamentalGroupEquivStabilizerOfLiftOverComposite A x

/-- The comparison retains the original pointed covering homomorphism. -/
theorem pointedCoverGroupEquivStabilizer_coe
    {S : Scheme.{u}} [ConnectedSpace S]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (A : FiniteEtale S) (x : Spec (.of Ω) ⟶ A.left)
    (xi : Spec (.of Ω) ⟶ S) (h : x ≫ A.hom = xi) (g : π₁ᵉᵗ(x)) :
    (pointedCoverGroupEquivStabilizer A x xi h g : π₁ᵉᵗ(xi)) =
      pointedFundamentalGroupHom A.hom x xi h g := by
  subst xi
  exact fundamentalGroupEquivStabilizerOfLift_coe A x g

variable {S T : Scheme.{u}} [ConnectedSpace S] [ConnectedSpace T]
variable {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
variable (AS : FiniteEtale S) (AT : FiniteEtale T)
variable (ξs : Spec (.of Ω₁) ⟶ S) (ξt : Spec (.of Ω₂) ⟶ T)
variable (xs : Spec (.of Ω₁) ⟶ AS.left) (xt : Spec (.of Ω₂) ⟶ AT.left)
variable (hs : xs ≫ AS.hom = ξs) (ht : xt ≫ AT.hom = ξt)
variable (α : π₁ᵉᵗ(ξs) ≃ₜ* π₁ᵉᵗ(ξt))
variable (e : (fiber ξs).obj AS ≃ (fiber ξt).obj AT)
variable (he : ∀ g x, e (g • x) = α g • e x)
variable (hpoint : e ((fiberObjEquivHom ξs AS).symm (Over.homMk xs hs)) =
  (fiberObjEquivHom ξt AT).symm (Over.homMk xt ht))

/-- The actual two covering groups are transported through the same base
equivalence and the same matched fibre points. -/
def pointedCoverGroupTransport : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt) :=
  (pointedCoverGroupEquivStabilizer AS xs ξs hs).trans
    ((MulAction.stabilizerContinuousMulEquivOfEquivariant α e he _ _ hpoint).trans
      (pointedCoverGroupEquivStabilizer AT xt ξt ht).symm)

/-- The inclusion square commutes with the original base-group equivalence,
not with a subsequently selected conjugate. -/
theorem pointedCoverGroupTransport_inclusion (g : π₁ᵉᵗ(xs)) :
    pointedFundamentalGroupHom AT.hom xt ξt ht
      (pointedCoverGroupTransport AS AT ξs ξt xs xt hs ht α e he hpoint g) =
        α (pointedFundamentalGroupHom AS.hom xs ξs hs g) := by
  rw [← pointedCoverGroupEquivStabilizer_coe]
  change ((pointedCoverGroupEquivStabilizer AT xt ξt ht)
    ((pointedCoverGroupEquivStabilizer AT xt ξt ht).symm
      (MulAction.stabilizerContinuousMulEquivOfEquivariant α e he _ _ hpoint
        (pointedCoverGroupEquivStabilizer AS xs ξs hs g))) : π₁ᵉᵗ(ξt)) = _
  rw [(pointedCoverGroupEquivStabilizer AT xt ξt ht).apply_symm_apply]
  change α (pointedCoverGroupEquivStabilizer AS xs ξs hs g : π₁ᵉᵗ(ξs)) = _
  rw [pointedCoverGroupEquivStabilizer_coe]

/-- In particular, every original compatible arithmetic quotient stays
compatible after passing to these actual pointed covers. -/
theorem pointedCoverGroupTransport_quotient
    {Γ : Type*} [Monoid Γ] (qs : π₁ᵉᵗ(ξs) →* Γ) (qt : π₁ᵉᵗ(ξt) →* Γ)
    (hq : ∀ a, qt (α a) = qs a) (g : π₁ᵉᵗ(xs)) :
    qt (pointedFundamentalGroupHom AT.hom xt ξt ht
      (pointedCoverGroupTransport AS AT ξs ξt xs xt hs ht α e he hpoint g)) =
        qs (pointedFundamentalGroupHom AS.hom xs ξs hs g) := by
  rw [pointedCoverGroupTransport_inclusion]
  exact hq _

end AlgebraicGeometry.FiniteEtale
