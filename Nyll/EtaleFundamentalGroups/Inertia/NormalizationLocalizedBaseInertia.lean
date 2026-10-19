/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationIntegralBaseInertia
import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaBaseLocalization

/-!
# Inertia after integral base enlargement and prime localization

The same original prime is first contracted through the canonical integral-base
equivalence and then extended to the literal localized normalization.
Its inertia equals the scalar-restriction comap of the original inertia.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe uA uB uR u

variable (A : Type uA) (B : Type uB) (R : Type uR) (F L Ω : Type u)
  [CommRing A] [CommRing B] [CommRing R] [IsLocalRing R]
  [Field F] [Field L] [Field Ω]
  [Algebra A B] [Algebra.IsIntegral A B]
  [Algebra A F] [IsFractionRing A F]
  [Algebra B L] [IsFractionRing B L]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [Algebra A Ω] [Algebra B Ω]
  [IsScalarTower F L Ω] [IsScalarTower A F Ω]
  [IsScalarTower B L Ω] [IsScalarTower A B Ω]
  [Algebra.IsAlgebraic F Ω] [IsGalois L Ω]
  [Algebra B R] [Algebra R L] [IsFractionRing R L] [Algebra R Ω]
  [IsScalarTower R L Ω] [IsScalarTower B R Ω]

local instance localizationOriginalAction :
    MulSemiringAction Gal(Ω/F) (integralClosure A Ω) :=
  IsIntegralClosure.MulSemiringAction A F Ω (integralClosure A Ω)

local instance localizationFinalAction :
    MulSemiringAction Gal(Ω/L) (integralClosure R Ω) :=
  IsIntegralClosure.MulSemiringAction R L Ω (integralClosure R Ω)

/-- The actual localized prime has precisely the original inertia restricted
to the larger fraction field. Both primes are literal comap/map constructions. -/
theorem normalizationLocalizedBase_inertia_comap
    (P : Ideal B) [P.IsPrime] [IsLocalization.AtPrime R P]
    (Q : Ideal (integralClosure A Ω)) [Q.IsPrime]
    (hQover : (Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom).LiesOver P) :
    let QB := Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom
    let q := QB.map (normalizationBaseLocalizationRingMap B R Ω)
    q.IsMaximal ∧
      (Q.inertia Gal(Ω/F)).comap (AlgEquiv.restrictScalarsHom F) =
        q.inertia Gal(Ω/L) := by
  intro QB q
  have : QB.IsPrime := Ideal.IsPrime.comap _
  have : QB.LiesOver P := hQover
  have hlocal := originalNormalizationInertia_eq_of_primeLocalization B R L Ω P QB
  refine ⟨hlocal.1, ?_⟩
  exact (normalizationIntegralBase_inertia_comap F L Q).trans hlocal.2

end EtaleFundamentalGroups.Inertia
