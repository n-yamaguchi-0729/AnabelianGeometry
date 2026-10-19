/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Ramification.GaloisPlaceFiber
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteNormalizationInertiaImage
import Nyll.EtaleFundamentalGroups.Inertia.SurjectiveActionDoubleCoset

/-!
# Actual extending places and double cosets of normalization inertia

The literal contracted prime selects the extending place. The supplied
finite quotient must agree with restriction on the same absolute field.
-/

noncomputable section

open AlgebraicCurve IsDedekindDomain

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

local instance absolutePlaceNormalizationAction :
    MulSemiringAction Gal(Ω/F) (integralClosure v.toValuationSubring Ω) :=
  IsIntegralClosure.MulSemiringAction v.toValuationSubring F Ω _

local instance finitePlaceNormalizationAction :
    MulSemiringAction Gal(L/F) (Place.integralClosureAt L v) :=
  IsIntegralClosure.MulSemiringAction v.toValuationSubring F L _

/-- For a finite quotient agreeing with the prescribed field restriction,
the actual place fibre is the double-coset space of the original inertia image. -/
def normalizationPlaceDoubleCosetEquiv
    {G : Type*} [Group G] (q : Gal(Ω/F) →* G) (ρ : G →* Gal(L/F))
    (hρ : Function.Surjective ρ)
    (hcomp : ρ.comp q = AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) L)
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [Q.IsPrime]
    (P : HeightOneSpectrum (Place.integralClosureAt L v))
    (hP : P.asIdeal = absoluteNormalizationPrimeContraction
      (A := v.toValuationSubring) (L := L) (Omega := Ω) Q) :
    DoubleCoset.Quotient (ρ.ker : Set G) ((Q.inertia Gal(Ω/F)).map q : Set G) ≃
      Place.galoisPlaceFiber (L := L) v := by
  let w₀ : Place.galoisPlaceFiber (L := L) v :=
    ⟨Place.placeOfPrime P, Place.restrict_placeOfPrime P⟩
  have hI : ((Q.inertia Gal(Ω/F)).map q).map ρ =
      MulAction.stabilizer Gal(L/F) w₀ := by
    rw [Subgroup.map_map, hcomp,
      absoluteNormalizationPrime_inertia_map_eq_contraction]
    rw [Place.galoisPlaceFiber_stabilizer_eq_inertia]
    change (absoluteNormalizationPrimeContraction
      (A := v.toValuationSubring) (L := L) (Omega := Ω) Q).inertia Gal(L/F) =
        (Place.fiberCenter L v (Place.restrict_placeOfPrime P)).asIdeal.inertia Gal(L/F)
    rw [Place.fiberCenter_placeOfPrime, hP]
  exact doubleCosetEquivOfSurjectiveAction ρ hρ ρ.ker
    ((Q.inertia Gal(Ω/F)).map q) rfl w₀ hI

/-- The equivalence sends each representative to its original field action
on the extending place selected by the same finite prime. -/
@[simp] theorem normalizationPlaceDoubleCosetEquiv_mk
    {G : Type*} [Group G] (q : Gal(Ω/F) →* G) (ρ : G →* Gal(L/F))
    (hρ : Function.Surjective ρ)
    (hcomp : ρ.comp q = AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) L)
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [Q.IsPrime]
    (P : HeightOneSpectrum (Place.integralClosureAt L v))
    (hP : P.asIdeal = absoluteNormalizationPrimeContraction
      (A := v.toValuationSubring) (L := L) (Omega := Ω) Q) (g : G) :
    normalizationPlaceDoubleCosetEquiv v q ρ hρ hcomp Q P hP
      (DoubleCoset.mk ρ.ker ((Q.inertia Gal(Ω/F)).map q) g) =
      ρ g • (⟨Place.placeOfPrime P, Place.restrict_placeOfPrime P⟩ :
        Place.galoisPlaceFiber (L := L) v) := rfl

end EtaleFundamentalGroups.Inertia
