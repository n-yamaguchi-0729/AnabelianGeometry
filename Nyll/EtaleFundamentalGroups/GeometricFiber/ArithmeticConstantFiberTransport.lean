/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticNaturality
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackFiberPoint

/-! # Constant fibres compared by the original arithmetic comparison

Use the very fibre comparison defining arithmeticFundamentalGroupHom. The
resulting equivalence of two actual constant-cover fibres is equivariant for
the original arithmetic group equivalence. A specified point in the common
constant fibre gives the two matched lifts, without choosing an unrelated
comparison or assuming preservation of an embedding of the finite field.
-/
noncomputable section
open CategoryTheory CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (k κ : Type u) [Field k] [Field κ] [Algebra k κ]
variable [IsSepClosure k κ] [IsSepClosed κ]

/-- The fibre comparison already used in the original arithmetic map. -/
def arithmeticConstantFiberEquiv
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    (A : FiniteEtale (Spec (.of k))) :
    (fiber xi).obj ((pullback f).obj A) ≃ (fib k κ).obj A :=
  FintypeCat.equivEquivIso.symm
    (((pullbackFiberIso f xi) ≪≫
      (nonempty_fiber_iso (xi ≫ f) (ξ k κ)).some).app A)

private theorem arithmeticMap_toAut
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    (g : π₁ᵉᵗ(xi)) :
    toAut (fib k κ) Gal(κ/k) (arithmeticFundamentalGroupHom k κ f xi g) =
      ((nonempty_fiber_iso (xi ≫ f) (ξ k κ)).some).conjAut
        (fundamentalGroupHom f xi g) := by
  let t : fiber (xi ≫ f) ≅ fib k κ :=
    (nonempty_fiber_iso (xi ≫ f) (ξ k κ)).some
  change (toAutHomeo (fib k κ) Gal(κ/k))
    ((toAutHomeo (fib k κ) Gal(κ/k)).symm
      ((continuousConjAut t) (fundamentalGroupHom f xi g))) = _
  exact (toAutHomeo (fib k κ) Gal(κ/k)).apply_symm_apply _

/-- Its action is the original arithmetic quotient, with no inner correction. -/
theorem arithmeticConstantFiberEquiv_smul
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    (A : FiniteEtale (Spec (.of k)))
    (g : π₁ᵉᵗ(xi)) (x : (fiber xi).obj ((pullback f).obj A)) :
    arithmeticConstantFiberEquiv k κ f xi A (g • x) =
      arithmeticFundamentalGroupHom k κ f xi g •
        arithmeticConstantFiberEquiv k κ f xi A x := by
  let t : fiber (xi ≫ f) ≅ fib k κ :=
    (nonempty_fiber_iso (xi ≫ f) (ξ k κ)).some
  have ht (a : π₁ᵉᵗ(xi ≫ f)) (y : (fiber (xi ≫ f)).obj A) :
      t.hom.app A (a.hom.app A y) =
        (t.conjAut a).hom.app A (t.hom.app A y) := by
    change t.hom.app A (a.hom.app A y) =
      t.hom.app A (a.hom.app A (t.inv.app A (t.hom.app A y)))
    exact congrArg (fun z => t.hom.app A (a.hom.app A z))
      (FintypeCat.hom_inv_id_apply (t.app A) y).symm
  change t.hom.app A ((pullbackFiberIso f xi).hom.app A (g.hom.app _ x)) =
    arithmeticFundamentalGroupHom k κ f xi g •
      t.hom.app A ((pullbackFiberIso f xi).hom.app A x)
  rw [pullbackFiberIso_hom_fundamentalGroupHom_apply]
  rw [← toAut_hom_app_apply (fib k κ)
    (arithmeticFundamentalGroupHom k κ f xi g), arithmeticMap_toAut]
  exact ht _ _

/-- The same arithmetic group equivalence transports actual constant covers
by using their common original constant fibre. -/
def arithmeticConstantCoverFiberTransport
    {Xs Xt : Scheme.{u}}
    (fs : Xs ⟶ Spec (.of k)) (ft : Xt ⟶ Spec (.of k))
    {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (xs : Spec (.of Ω₁) ⟶ Xs) (xt : Spec (.of Ω₂) ⟶ Xt)
    (A : FiniteEtale (Spec (.of k))) :
    (fiber xs).obj ((pullback fs).obj A) ≃ (fiber xt).obj ((pullback ft).obj A) :=
  (arithmeticConstantFiberEquiv k κ fs xs A).trans
    (arithmeticConstantFiberEquiv k κ ft xt A).symm

/-- Full arithmetic equivariance follows from the original quotient equality. -/
theorem arithmeticConstantCoverFiberTransport_smul
    {Xs Xt : Scheme.{u}}
    (fs : Xs ⟶ Spec (.of k)) (ft : Xt ⟶ Spec (.of k))
    {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (xs : Spec (.of Ω₁) ⟶ Xs) (xt : Spec (.of Ω₂) ⟶ Xt)
    (α : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt))
    (hα : ∀ g, arithmeticFundamentalGroupHom k κ ft xt (α g) =
      arithmeticFundamentalGroupHom k κ fs xs g)
    (A : FiniteEtale (Spec (.of k)))
    (g : π₁ᵉᵗ(xs)) (x : (fiber xs).obj ((pullback fs).obj A)) :
    arithmeticConstantCoverFiberTransport k κ fs ft xs xt A (g • x) =
      α g • arithmeticConstantCoverFiberTransport k κ fs ft xs xt A x := by
  apply (arithmeticConstantFiberEquiv k κ ft xt A).injective
  change arithmeticConstantFiberEquiv k κ ft xt A
      ((arithmeticConstantFiberEquiv k κ ft xt A).symm
        (arithmeticConstantFiberEquiv k κ fs xs A (g • x))) = _
  rw [Equiv.apply_symm_apply, arithmeticConstantFiberEquiv_smul,
    arithmeticConstantFiberEquiv_smul, hα]
  change _ = arithmeticFundamentalGroupHom k κ fs xs g •
    arithmeticConstantFiberEquiv k κ ft xt A
      ((arithmeticConstantFiberEquiv k κ ft xt A).symm
        (arithmeticConstantFiberEquiv k κ fs xs A x))
  rw [Equiv.apply_symm_apply]

omit [IsSepClosure k κ] in
/-- A single specified constant-fibre point supplies both matched lifts. -/
theorem arithmeticConstantCoverFiberTransport_matched_point
    {Xs Xt : Scheme.{u}}
    (fs : Xs ⟶ Spec (.of k)) (ft : Xt ⟶ Spec (.of k))
    {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (xs : Spec (.of Ω₁) ⟶ Xs) (xt : Spec (.of Ω₂) ⟶ Xt)
    (A : FiniteEtale (Spec (.of k))) (z : (fib k κ).obj A) :
    arithmeticConstantCoverFiberTransport k κ fs ft xs xt A
        ((arithmeticConstantFiberEquiv k κ fs xs A).symm z) =
      (arithmeticConstantFiberEquiv k κ ft xt A).symm z := by
  change (arithmeticConstantFiberEquiv k κ ft xt A).symm
      (arithmeticConstantFiberEquiv k κ fs xs A
        ((arithmeticConstantFiberEquiv k κ fs xs A).symm z)) = _
  rw [Equiv.apply_symm_apply]

end AlgebraicGeometry.FiniteEtale
