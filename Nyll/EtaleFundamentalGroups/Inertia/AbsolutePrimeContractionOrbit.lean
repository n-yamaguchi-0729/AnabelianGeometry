/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteNormalizationPrime
import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationGaloisInvariant
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Invariant.Profinite

/-! # Absolute prime orbits cover every finite normalization prime -/

noncomputable section
open AlgebraicCurve IsDedekindDomain
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

universe u

variable {k F L Ω : Type u} [Field k] [Field F] [Field L] [Field Ω]
    [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsSepClosure F Ω]
    (v : Place k F) [Algebra v.toValuationSubring Ω]
    [IsScalarTower v.toValuationSubring F Ω] [IsScalarTower v.toValuationSubring L Ω]

attribute [local instance] Place.instIsDedekindDomainIntegralClosureAt

local instance absolutePrimeLiftAction :
    MulSemiringAction Gal(Ω/F) (integralClosure v.toValuationSubring Ω) :=
  IsIntegralClosure.MulSemiringAction v.toValuationSubring F Ω _

omit [Algebra k L] [IsScalarTower k F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [IsScalarTower F L Ω] in
/-- Every finite prime is the contraction of a translate of one fixed absolute prime. -/
theorem exists_smul_absoluteNormalizationPrimeContraction_eq
    (P : HeightOneSpectrum (Place.integralClosureAt L v))
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [Q.IsMaximal] :
    ∃ σ : Gal(Ω/F), absoluteNormalizationPrimeContraction
      (A := v.toValuationSubring) (L := L) (Omega := Ω) (σ • Q) = P.asIdeal := by
  let A := v.toValuationSubring
  let B := Place.integralClosureAt L v
  let C := integralClosure A Ω
  let f : B →ₐ[A] C :=
    finiteNormalizationToAbsoluteNormalization (A := A) (L := L) (Omega := Ω)
  let : Algebra B C := f.toRingHom.toAlgebra
  have : IsScalarTower A B C :=
    IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  have : Algebra.IsIntegral B C := Algebra.IsIntegral.tower_top A
  have : P.asIdeal.IsMaximal := P.isPrime.isMaximal P.ne_bot
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply (algebraMap L Ω).injective
    exact congrArg Subtype.val h
  obtain ⟨Q', hQ'max, hQ'⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := C) P.asIdeal (by
      change RingHom.ker f.toRingHom ≤ P.asIdeal
      rw [(RingHom.injective_iff_ker_eq_bot f.toRingHom).mp hf]
      exact bot_le)
  have : Q'.IsMaximal := hQ'max
  let : TopologicalSpace C := ⊥
  have : DiscreteTopology C := ⟨rfl⟩
  have : ContinuousSMul Gal(Ω/F) C := integralClosure_continuousSMul_krull A F Ω
  have : Algebra.IsInvariant A C Gal(Ω/F) := integralClosure_isInvariant_of_isGalois A F Ω
  have : SMulCommClass Gal(Ω/F) A C :=
    ⟨fun σ a b => (galRestrict A F Ω C σ).toLinearEquiv.map_smul a b⟩
  have hunder : Q.under A = Q'.under A :=
    (IsLocalRing.eq_maximalIdeal (inferInstance : (Q.under A).IsMaximal)).trans
      (IsLocalRing.eq_maximalIdeal (inferInstance : (Q'.under A).IsMaximal)).symm
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := A) (B := C) (G := Gal(Ω/F)) Q Q' hunder
  refine ⟨σ, ?_⟩
  rw [← hσ]
  exact hQ'

end EtaleFundamentalGroups.Inertia
