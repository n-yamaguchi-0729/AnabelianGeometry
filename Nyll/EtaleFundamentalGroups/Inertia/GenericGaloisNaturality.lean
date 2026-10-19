/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.GenericGaloisMapComparison
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisNaturality
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps

/-!
# The exact generic Galois square for a pointed scheme morphism

The canonical pointed map uses precisely the supplied geometric-point
equality and the original absolute generic Galois homomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.Inertia

universe u

private theorem pointedHom_eq_equality_conjugation
    {X Y : Scheme.{u}} {Ω : Type u} [Field Ω]
    (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y)
    (h : x ≫ f = y) (a : π₁ᵉᵗ(x)) :
    pointedFundamentalGroupHom f x y h a =
      continuousConjAut (eqToIso (congrArg fiber h)) (fundamentalGroupHom f x a) := by
  subst y
  rfl

/-- The pointed morphism and the original absolute generic Galois map
commute with scalar restriction for the same ambient geometric point. -/
theorem pointedFundamentalGroupHom_fieldSource_eq_absoluteGenericGalois
    {U V : Scheme.{u}} [IsIntegral U] [IsIntegral V]
    (L Ω : Type u) [Field L] [Field Ω]
    [Algebra U.functionField L] [Algebra U.functionField Ω] [Algebra L Ω]
    [IsScalarTower U.functionField L Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosure L Ω] [IsSepClosed Ω]
    (f : V ⟶ U) (jL : Spec (.of L) ⟶ V)
    (hpoint : (ξ L Ω ≫ jL) ≫ f = U.genericExtensionMorphism Ω)
    (σ : Gal(Ω/L)) :
    pointedFundamentalGroupHom f (ξ L Ω ≫ jL) (U.genericExtensionMorphism Ω) hpoint
        (fieldSourceAbsoluteGaloisHom L Ω jL σ) =
      absoluteGenericGaloisToFundamentalGroup U Ω (σ.restrictScalars U.functionField) := by
  rw [pointedHom_eq_equality_conjugation,
    absoluteGenericGaloisToFundamentalGroup_eq_fieldSourceAbsoluteGaloisHom]
  exact fieldSourceAbsoluteGaloisHom_naturality U.functionField L Ω f jL
    (U.fromSpecStalk (genericPoint U)) hpoint σ

end EtaleFundamentalGroups.Inertia
