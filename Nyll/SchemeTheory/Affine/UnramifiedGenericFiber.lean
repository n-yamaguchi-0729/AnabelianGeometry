/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.GenericFiber.Unramified
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual generic-fiber squares of affine integral schemes

The generic-fiber square is a pullback when the source and base have
compatible fraction fields and the algebra map is essentially finite type
and formally unramified.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups

universe u

/-- For a dominant essentially finite type unramified map of affine integral
schemes, the actual generic fibre is the source fraction-field spectrum. -/
theorem isPullback_spec_unramified_generic
    (R S K E : Type u)
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field E] [Algebra S E] [IsFractionRing S E]
    [Algebra R E] [IsScalarTower R S E]
    [Algebra K E] [IsScalarTower R K E] :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap S E)))
      (Spec.map (CommRingCat.ofHom (algebraMap K E)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have : Algebra.IsPushout R S K E :=
    (unramifiedGenericFiber_isPushout (R := R) (S := S) (K := K) (E := E)).symm
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R S K E)

end EtaleFundamentalGroups
