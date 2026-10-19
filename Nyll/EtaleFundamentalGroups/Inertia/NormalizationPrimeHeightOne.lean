/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteNormalizationPrime
import Mathlib.RingTheory.Ideal.GoingUp

/-! # The actual finite height-one prime under a maximal absolute prime -/

noncomputable section

open AlgebraicCurve IsDedekindDomain

namespace EtaleFundamentalGroups.Inertia

universe u

variable {k F L Ω : Type u} [Field k] [Field F] [Field L] [Field Ω]
  [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L]
  [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω]
  (v : Place k F) [Algebra v.toValuationSubring Ω]
  [IsScalarTower v.toValuationSubring F Ω]
  [IsScalarTower v.toValuationSubring L Ω]

attribute [local instance] Place.instIsDedekindDomainIntegralClosureAt

omit [Algebra k L] [IsScalarTower k F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L]
  [Algebra F Ω] [IsScalarTower F L Ω]
  [IsScalarTower v.toValuationSubring F Ω] in
/-- A maximal absolute normalization prime contracts to a literal finite
height-one prime, with no replacement of the given field embedding. -/
theorem exists_heightOneSpectrum_absoluteNormalizationPrimeContraction
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [Q.IsMaximal] :
    ∃ P : HeightOneSpectrum (Place.integralClosureAt L v),
      P.asIdeal = absoluteNormalizationPrimeContraction
        (A := v.toValuationSubring) (L := L) (Omega := Ω) Q := by
  let : Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring) :=
    ⟨(IsLocalRing.eq_maximalIdeal
      (inferInstance : (Q.under v.toValuationSubring).IsMaximal)).symm⟩
  let q : Ideal (Place.integralClosureAt L v) :=
    absoluteNormalizationPrimeContraction
      (A := v.toValuationSubring) (L := L) (Omega := Ω) Q
  have : q.IsPrime := by
    dsimp [q]
    infer_instance
  have : q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring) := by
    dsimp [q]
    infer_instance
  have hqmax : q.IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal q
      (IsLocalRing.maximalIdeal v.toValuationSubring)
  have hqne : q ≠ ⊥ := by
    intro h
    apply Place.maximalIdeal_ne_bot v
    have h2 := q.over_def (IsLocalRing.maximalIdeal v.toValuationSubring)
    rw [h, Ideal.under_def, Ideal.comap_bot_of_injective _
      (Place.algebraMap_integralClosureAt_injective v)] at h2
    exact h2
  exact ⟨⟨q, hqmax.isPrime, hqne⟩, rfl⟩

end EtaleFundamentalGroups.Inertia
