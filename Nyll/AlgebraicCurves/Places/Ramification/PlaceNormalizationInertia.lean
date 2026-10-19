/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Ramification.PlaceFiberCenterEquivariance
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.EtaleFundamentalGroups.Inertia.HenselianIntegralFiberAction

/-!
# Actual finite place stabilizers are normalization inertia

Finite residue fields over the algebraically closed constant field are
separably closed. The existing inertia–prime-stabilizer theorem and the
actual place–prime equivariance therefore identify the place stabilizer.
-/

noncomputable section

open IsDedekindDomain
open scoped Pointwise

namespace AlgebraicCurve.Place

variable {k F L : Type*} [Field k] [IsAlgClosed k] [Field F] [Field L]
  [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
  [IsCurveOver k F] [FiniteDimensional F L] [Algebra.IsSeparable F L]
  (v : Place k F)

local instance placeInertiaNormalizationAction :
    MulSemiringAction Gal(L/F) (integralClosureAt L v) :=
  IsIntegralClosure.MulSemiringAction v.toValuationSubring F L (integralClosureAt L v)

/-- For the actual extending place, fixing the place is exactly inertia
membership at its literal normalization prime. -/
theorem mem_normalizationInertia_iff_fix_placeOfPrime
    (P : HeightOneSpectrum (integralClosureAt L v)) (σ : Gal(L/F)) :
    σ ∈ P.asIdeal.inertia Gal(L/F) ↔
      SemilinearAut.ofAlgAut (σ.restrictScalars k) • placeOfPrime P =
        placeOfPrime P := by
  have : Module.Finite k v.ResidueField := IsCurveOver.finite_residueField v
  have : Algebra.IsIntegral k v.ResidueField := Algebra.IsIntegral.of_finite k v.ResidueField
  have : IsSepClosed v.ResidueField :=
    Algebra.IsAlgebraic.isSepClosed (F := k) (E := v.ResidueField)
  have : P.asIdeal.IsPrime := P.isPrime
  have : P.asIdeal.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring) := by
    simpa only [fiberCenter_placeOfPrime] using
      (fiberCenter_liesOver (restrict_placeOfPrime P))
  have : SMulCommClass Gal(L/F) v.toValuationSubring (integralClosureAt L v) :=
    ⟨fun σ a b =>
      (galRestrict v.toValuationSubring F L (integralClosureAt L v) σ).toLinearEquiv.map_smul a b⟩
  have hI :=
    EtaleFundamentalGroups.Inertia.inertia_eq_stabilizer_of_integral_of_residue_isSepClosed
      v.toValuationSubring (integralClosureAt L v) Gal(L/F) P.asIdeal
  rw [hI]
  change σ • P.asIdeal = P.asIdeal ↔ _
  exact placeOfPrime_stabilizer_iff v P σ

/-- The same identification at the center of any specified extending place. -/
theorem mem_fiberCenter_inertia_iff_fix_place
    (w : Place k L) (hw : w.restrict F = v) (σ : Gal(L/F)) :
    σ ∈ (fiberCenter L v hw).asIdeal.inertia Gal(L/F) ↔
      SemilinearAut.ofAlgAut (σ.restrictScalars k) • w = w := by
  have hplace : placeOfPrime (fiberCenter L v hw) = w :=
    eq_of_fiberCenter_eq (restrict_placeOfPrime _) hw (fiberCenter_placeOfPrime _)
  simpa only [hplace] using
    mem_normalizationInertia_iff_fix_placeOfPrime v (fiberCenter L v hw) σ

end AlgebraicCurve.Place
