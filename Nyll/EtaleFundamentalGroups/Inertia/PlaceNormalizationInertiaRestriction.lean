/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationLocalizedBaseInertia
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationIntegralBaseContraction

/-!
# Restricting normalization inertia to an actual extending place

The extending valuation ring is the localization at the prescribed finite
normalization prime. No replacement prime or abstract inertia is chosen.
-/

noncomputable section

open IsDedekindDomain AlgebraicCurve

namespace EtaleFundamentalGroups.Inertia

universe u

variable {k F L Ω : Type u} [Field k] [Field F] [Field L] [Field Ω]
  [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L]
  [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω]
  [Algebra.IsAlgebraic F Ω] [IsGalois L Ω]
  (v : Place k F)

local instance placeBaseAmbientAlgebra : Algebra v.toValuationSubring Ω :=
  Algebra.ofSubsemiring v.toValuationSubring

local instance placeBaseAmbientTower : IsScalarTower v.toValuationSubring F Ω :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

local instance extendingPlaceAmbientAlgebra (w : Place k L) :
    Algebra w.toValuationSubring Ω := Algebra.ofSubsemiring w.toValuationSubring

local instance extendingPlaceAmbientTower (w : Place k L) :
    IsScalarTower w.toValuationSubring L Ω :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

local instance finiteNormalizationPlaceAlgebra
    (P : HeightOneSpectrum (Place.integralClosureAt L v)) :
    Algebra (Place.integralClosureAt L v) (Place.placeOfPrime P).toValuationSubring := by
  change Algebra (Place.integralClosureAt L v)
    (HeightOneSpectrum.valuationSubringAtPrime L P)
  infer_instance

local instance finiteNormalizationPlaceTower
    (P : HeightOneSpectrum (Place.integralClosureAt L v)) :
    IsScalarTower (Place.integralClosureAt L v) (Place.placeOfPrime P).toValuationSubring L := by
  change IsScalarTower (Place.integralClosureAt L v)
    (HeightOneSpectrum.valuationSubringAtPrime L P) L
  infer_instance

local instance finiteNormalizationPlaceLocalization
    (P : HeightOneSpectrum (Place.integralClosureAt L v)) :
    IsLocalization.AtPrime (Place.placeOfPrime P).toValuationSubring P.asIdeal := by
  change IsLocalization.AtPrime (HeightOneSpectrum.valuationSubringAtPrime L P) P.asIdeal
  infer_instance

local instance finiteNormalizationPlaceAmbientTower
    (P : HeightOneSpectrum (Place.integralClosureAt L v)) :
    IsScalarTower (Place.integralClosureAt L v) (Place.placeOfPrime P).toValuationSubring Ω := by
  let B := Place.integralClosureAt L v
  let R := (Place.placeOfPrime P).toValuationSubring
  apply IsScalarTower.of_algebraMap_eq
  intro b
  change algebraMap L Ω (algebraMap B L b) =
    algebraMap L Ω (algebraMap R L (algebraMap B R b))
  exact congrArg (algebraMap L Ω) (IsScalarTower.algebraMap_apply B R L b)

local instance originalPlaceNormalizationAction :
    MulSemiringAction Gal(Ω/F) (integralClosure v.toValuationSubring Ω) :=
  IsIntegralClosure.MulSemiringAction v.toValuationSubring F Ω _

local instance extendingPlaceNormalizationAction (w : Place k L) :
    MulSemiringAction Gal(Ω/L) (integralClosure w.toValuationSubring Ω) :=
  IsIntegralClosure.MulSemiringAction w.toValuationSubring L Ω _

/-- At the same finite normalization prime, actual place inertia is the
scalar-restriction comap of the original normalization inertia. -/
theorem placeOfPrime_normalization_inertia_comap
    (P : HeightOneSpectrum (Place.integralClosureAt L v))
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [Q.IsPrime]
    (hP : P.asIdeal = absoluteNormalizationPrimeContraction
      (A := v.toValuationSubring) (L := L) (Omega := Ω) Q) :
    let R := (Place.placeOfPrime P).toValuationSubring
    let QB := Q.comap (normalizationIntegralBaseRingEquiv
      v.toValuationSubring (Place.integralClosureAt L v) Ω).toRingHom
    let q := QB.map
      (normalizationBaseLocalizationRingMap (Place.integralClosureAt L v) R Ω)
    q.IsMaximal ∧
      (Q.inertia Gal(Ω/F)).comap (AlgEquiv.restrictScalarsHom F) =
        q.inertia Gal(Ω/L) := by
  let B := Place.integralClosureAt L v
  let R := (Place.placeOfPrime P).toValuationSubring
  have : P.asIdeal.IsPrime := P.isPrime
  have hQover : (Q.comap
      (normalizationIntegralBaseRingEquiv v.toValuationSubring B Ω).toRingHom).LiesOver
        P.asIdeal := by
    constructor
    rw [normalizationIntegralBase_contraction_eq]
    exact hP
  exact normalizationLocalizedBase_inertia_comap
    v.toValuationSubring B R F L Ω P.asIdeal Q hQover

end EtaleFundamentalGroups.Inertia
