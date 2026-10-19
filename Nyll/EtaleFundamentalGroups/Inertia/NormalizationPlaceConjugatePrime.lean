/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Ramification.GaloisPlaceFiber
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteNormalizationInertiaImage
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationPlaceDoubleCoset
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationPrimeContractionEquivariance

/-!
# Actual extending places and double cosets of normalization inertia

The literal contracted prime selects the extending place. The supplied
finite quotient must agree with restriction on the same absolute field.
-/

noncomputable section

open AlgebraicCurve IsDedekindDomain
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

attribute [local instance] Place.instIsPrimeCenter Place.instIsFractionRingIntegralClosureAt
  Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  Place.instIsDedekindDomainIntegralClosureAt
  Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt

universe u

variable {k F L Ω : Type u} [Field k] [IsAlgClosed k] [Field F] [Field L] [Field Ω]
  [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
  [IsCurveOver k F] [FiniteDimensional F L] [IsGalois F L]
  [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsSepClosure F Ω]
  (v : Place k F) [Algebra v.toValuationSubring Ω]
  [IsScalarTower v.toValuationSubring F Ω] [IsScalarTower v.toValuationSubring L Ω]

local instance translatedAbsolutePlaceAction :
    MulSemiringAction Gal(Ω/F) (integralClosure v.toValuationSubring Ω) :=
  IsIntegralClosure.MulSemiringAction v.toValuationSubring F Ω _

local instance translatedFinitePlaceAction :
    MulSemiringAction Gal(L/F) (Place.integralClosureAt L v) :=
  IsIntegralClosure.MulSemiringAction v.toValuationSubring F L _

/-- A lifted representative selects the literal contraction of the translated prime. -/
theorem normalizationPlaceDoubleCosetEquiv_mk_fiberCenter
    {G : Type*} [Group G] (q : Gal(Ω/F) →* G) (ρ : G →* Gal(L/F))
    (hρ : Function.Surjective ρ)
    (hcomp : ρ.comp q = AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) L)
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [Q.IsPrime]
    (P : HeightOneSpectrum (Place.integralClosureAt L v))
    (hP : P.asIdeal = absoluteNormalizationPrimeContraction
      (A := v.toValuationSubring) (L := L) (Omega := Ω) Q)
    (σ : Gal(Ω/F)) :
    let z := normalizationPlaceDoubleCosetEquiv v q ρ hρ hcomp Q P hP
      (DoubleCoset.mk ρ.ker ((Q.inertia Gal(Ω/F)).map q) (q σ))
    (Place.fiberCenter L v z.property).asIdeal =
      absoluteNormalizationPrimeContraction
        (A := v.toValuationSubring) (L := L) (Omega := Ω) (σ • Q) := by
  dsimp only
  rw [normalizationPlaceDoubleCosetEquiv_mk]
  have hρσ : ρ (q σ) =
      AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) L σ :=
    congrArg (fun f : Gal(Ω/F) →* Gal(L/F) => f σ) hcomp
  rw [hρσ]
  change (Place.fiberCenter L v
    ((Place.restrict_ofAlgAut_smul
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) L σ)
      (Place.placeOfPrime P)).trans (Place.restrict_placeOfPrime P))).asIdeal = _
  rw [Place.fiberCenter_ofAlgAut_smul_asIdeal, Place.fiberCenter_placeOfPrime,
    hP, absoluteNormalizationPrimeContraction_smul]
  exact Place.restrict_placeOfPrime P

end EtaleFundamentalGroups.Inertia
