/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationIntegralBaseInertia
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteNormalizationPrime

/-!
# The same contracted prime after integral base comparison

For the finite normalization base B, the prime obtained by the canonical
integral-base equivalence contracts to the same literal prime used by the
pointed finite-cover inertia image theorem.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe uA u

/-- Integral base comparison preserves the prescribed finite normalization
contraction, without choosing another prime. -/
theorem normalizationIntegralBase_contraction_eq
    {A : Type uA} {L Ω : Type u}
    [CommRing A] [Field L] [Field Ω]
    [Algebra A L] [Algebra L Ω] [Algebra A Ω] [IsScalarTower A L Ω]
    (Q : Ideal (integralClosure A Ω)) :
    (Q.comap (normalizationIntegralBaseRingEquiv A (integralClosure A L) Ω).toRingHom).under
      (integralClosure A L) =
      absoluteNormalizationPrimeContraction (A := A) (L := L) (Omega := Ω) Q := by
  let B := integralClosure A L
  let e := normalizationIntegralBaseRingEquiv A B Ω
  apply Ideal.ext
  intro b
  change e (algebraMap B (integralClosure B Ω) b) ∈ Q ↔
    finiteNormalizationToAbsoluteNormalization (A := A) (L := L) (Omega := Ω) b ∈ Q
  have he :
      e (algebraMap B (integralClosure B Ω) b) =
        finiteNormalizationToAbsoluteNormalization (A := A) (L := L) (Omega := Ω) b := by
    apply Subtype.ext
    calc
      algebraMap (integralClosure A Ω) Ω
          (e (algebraMap B (integralClosure B Ω) b)) =
        algebraMap (integralClosure B Ω) Ω
          (algebraMap B (integralClosure B Ω) b) :=
        normalizationIntegralBaseRingEquiv_toAmbient A B Ω _
      _ = algebraMap B Ω b :=
        (IsScalarTower.algebraMap_apply B (integralClosure B Ω) Ω b).symm
      _ = algebraMap L Ω (algebraMap B L b) :=
        IsScalarTower.algebraMap_apply B L Ω b
      _ = algebraMap (integralClosure A Ω) Ω
          (finiteNormalizationToAbsoluteNormalization
            (A := A) (L := L) (Omega := Ω) b) := rfl
  rw [he]

end EtaleFundamentalGroups.Inertia
