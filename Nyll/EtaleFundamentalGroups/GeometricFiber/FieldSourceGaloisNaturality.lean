/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisPoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.ExtendedFiberGaloisAction
import Nyll.EtaleFundamentalGroups.GeometricFiber.HenselianSpecializationConjugacy

/-!
# Naturality of the actual field-source Galois homomorphism

The same ambient field automorphism acts on every geometric point by its
literal spectrum map. Equality transport therefore gives the exact square.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- The field-source Galois maps commute with a scheme morphism and the
specified equality of geometric points, without an additional conjugator. -/
theorem fieldSourceAbsoluteGaloisHom_naturality
    (F L Ω : Type u) [Field F] [Field L] [Field Ω]
    [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω]
    [IsSepClosure F Ω] [IsSepClosure L Ω] [IsSepClosed Ω]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    (jL : Spec (.of L) ⟶ Y) (jF : Spec (.of F) ⟶ X)
    (hpoint : (ξ L Ω ≫ jL) ≫ f = ξ F Ω ≫ jF)
    (σ : Gal(Ω/L)) :
    continuousConjAut (eqToIso (congrArg fiber hpoint))
      (fundamentalGroupHom f (ξ L Ω ≫ jL)
        (fieldSourceAbsoluteGaloisHom L Ω jL σ)) =
      fieldSourceAbsoluteGaloisHom F Ω jF (σ.restrictScalars F) := by
  have hL := fundamentalGroupHom_point_of_point_action
    jL (ξ L Ω) (suppliedGaloisEquivFundamentalGroup L Ω σ)
    σ.toRingHom (suppliedGaloisEquivFundamentalGroup_point L Ω σ)
  have hf := fundamentalGroupHom_point_of_point_action
    f (ξ L Ω ≫ jL) (fieldSourceAbsoluteGaloisHom L Ω jL σ)
    σ.toRingHom hL
  have hF := fundamentalGroupHom_point_of_point_action
    jF (ξ F Ω)
    (suppliedGaloisEquivFundamentalGroup F Ω (σ.restrictScalars F))
    (σ.restrictScalars F).toRingHom
    (suppliedGaloisEquivFundamentalGroup_point F Ω (σ.restrictScalars F))
  apply Aut.ext
  ext Z z
  apply (fiberObjEquivHom (ξ F Ω ≫ jF) Z).injective
  apply Over.OverMorphism.ext
  exact (point_action_of_eqToIso hpoint _ σ.toRingHom hf Z z).trans (hF Z z).symm

end AlgebraicGeometry.FiniteEtale
