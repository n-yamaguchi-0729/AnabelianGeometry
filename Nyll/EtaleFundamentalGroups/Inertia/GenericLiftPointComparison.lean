/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteDivisorialFiniteQuotientNaturality

/-!
# The rebased generic lift is the original pointed fibre element

Equality transport preserves the literal geometric lift used in the
pointed quotient and in its function-field embedding.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.Inertia

universe u

private theorem rebase_equality_fiber_iso
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] {U : Scheme.{u}}
    {s t : Spec (.of Ω) ⟶ U} (h : s = t)
    (W : FiniteEtale U) (w : (fiber t).obj W)
    (e : fiber s ≅ fiber t) (he : e = eqToIso (congrArg fiber h)) :
    genericPointLiftRebase h W (fiberObjEquivHom s W (e.inv.app W w)) =
      fiberObjEquivHom t W w := by
  subst e
  subst t
  apply Over.OverMorphism.ext
  rfl

private theorem symm_equality_iso
    {C : Type*} [Category C] {X Y : C} (p : Y = X) (q : X = Y) :
    (eqToIso p).symm = eqToIso q := by
  cases q
  rfl

/-- The rebased lift selecting the finite field is the originally chosen
point of the same covering fibre. -/
theorem genericPointLiftRebase_absoluteGenericFiberIso
    {U : Scheme.{u}} [IsIntegral U]
    (Ω : Type u) [Field Ω] [Algebra U.functionField Ω] [IsSepClosed Ω]
    (h : ξ U.functionField Ω ≫ U.genericExtensionMorphism U.functionField =
      U.genericExtensionMorphism Ω)
    (W : FiniteEtale U) (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
    genericPointLiftRebase h W
      (fiberObjEquivHom
        (ξ U.functionField Ω ≫ U.genericExtensionMorphism U.functionField) W
        ((absoluteGenericFiberIso U Ω).inv.app W w)) =
      fiberObjEquivHom (U.genericExtensionMorphism Ω) W w := by
  exact rebase_equality_fiber_iso h W w (absoluteGenericFiberIso U Ω)
    (symm_equality_iso _ _)

end EtaleFundamentalGroups.Inertia
