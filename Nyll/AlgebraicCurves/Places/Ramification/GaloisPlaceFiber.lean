/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Ramification.PlaceNormalizationInertia
import Nyll.AlgebraicCurves.Places.Restriction.RestrictionComposition
import Nyll.AlgebraicCurves.Places.Restriction.AlgEquivSmulEqRestrictEq
import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# The actual Galois fibre of extending places

The native field action preserves restriction, acts transitively on the
extending places, and has the literal finite normalization inertia stabilizer.
-/

noncomputable section

open IsDedekindDomain

namespace AlgebraicCurve.Place

attribute [local instance] instIsPrimeCenter instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt

variable {k F L : Type*} [Field k] [Field F] [Field L]
  [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]

/-- Galois automorphisms act through their original semilinear place action. -/
instance galoisPlaceAction : MulAction Gal(L/F) (Place k L) :=
  MulAction.compHom (Place k L)
    ((SemilinearAut.ofAlgAut (K := k) (F := L)).comp (AlgEquiv.restrictScalarsHom k))

variable [FiniteDimensional F L] [IsGalois F L]

/-- Places above the prescribed base place, with the inherited Galois action. -/
def galoisPlaceFiber (v : Place k F) : SubMulAction Gal(L/F) (Place k L) where
  carrier := {w | w.restrict F = v}
  smul_mem' := by
    intro σ w hw
    exact (restrict_ofAlgAut_smul σ w).trans hw

/-- The actual extending-place fibre is a transitive Galois set. -/
instance galoisPlaceFiber_pretransitive (v : Place k F) :
    MulAction.IsPretransitive Gal(L/F) (galoisPlaceFiber (L := L) v) := by
  constructor
  intro w z
  obtain ⟨σ, hσ⟩ := exists_algEquiv_smul_eq_of_restrict_eq w.val z.val
    (z.property.trans w.property.symm)
  exact ⟨σ, Subtype.ext hσ⟩

variable [IsAlgClosed k] [IsCurveOver k F] (v : Place k F)

local instance fibreNormalizationAction :
    MulSemiringAction Gal(L/F) (integralClosureAt L v) :=
  IsIntegralClosure.MulSemiringAction v.toValuationSubring F L (integralClosureAt L v)

/-- The stabilizer of an actual extending place is its finite normalization inertia. -/
theorem galoisPlaceFiber_stabilizer_eq_inertia
    (w : galoisPlaceFiber (L := L) v) :
    MulAction.stabilizer Gal(L/F) w =
      (fiberCenter L v w.property).asIdeal.inertia Gal(L/F) := by
  ext σ
  change σ • w = w ↔ σ ∈ (fiberCenter L v w.property).asIdeal.inertia Gal(L/F)
  constructor
  · intro h
    apply (mem_fiberCenter_inertia_iff_fix_place v w.val w.property σ).mpr
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact (mem_fiberCenter_inertia_iff_fix_place v w.val w.property σ).mp h

end AlgebraicCurve.Place
