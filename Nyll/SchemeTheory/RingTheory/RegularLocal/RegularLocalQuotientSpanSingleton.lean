/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsRegularLocalRing_quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.RingTheory.RegularLocal.QuotientRegular
public import Nyll.SchemeTheory.RingTheory.Dimension.LocalRingPrincipalQuotient
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain
public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ring.RingNF

/-!
# Is Regular Local Ring quotient span singleton of not Mem sq of forall minimal Primes not
Mem
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsRegularLocalRing_quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem

open IsLocalRing RingTheory
open scoped Pointwise

namespace W2RLR

universe u v

theorem maximalIdeal_ne_bot_of_ringKrullDim_pos (R : Type u) [CommRing R] [IsLocalRing R] (hdim : 0
  < ringKrullDim R) :
    maximalIdeal R ≠ ⊥ := by
  intro hbot
  rw [ringKrullDim_eq_zero_of_isField
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)] at hdim
  exact hdim.false

namespace No4PatchingCore

section FromABFreeness
variable {R : Type u} [CommRing R]

theorem isLocalRing_quotient_span_singleton [IsLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) : IsLocalRing (R ⧸ Ideal.span {x}) :=
  RegularQuotientEngine.isLocalRing_quotient_span_singleton R hx

theorem exists_ringKrullDim_eq_natCast (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] : ∃ d : ℕ, ringKrullDim R = (d : WithBot ℕ∞) :=
  RegularQuotientEngine.exists_ringKrullDim_eq_natCast R

end FromABFreeness

section Exchange0
variable (R : Type u) [CommRing R]

theorem exists_finite_span_eq_maximalIdeal_mem [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    ∃ S : Set R, x ∈ S ∧ S.Finite ∧ S.ncard ≤ (maximalIdeal R).spanFinrank ∧
      Ideal.span S = maximalIdeal R :=
  RegularQuotientEngine.exists_span_eq_maximalIdeal_ncard_le R hx hx2

end Exchange0

section PrimeAvoidance

theorem maximalIdeal_notMem_minimalPrimes_of_ringKrullDim_pos
    (R : Type u) [CommRing R] [IsLocalRing R] (hdim : 0 < ringKrullDim R) :
    maximalIdeal R ∉ minimalPrimes R := by
  intro hmem
  have hall : ∀ p : PrimeSpectrum R, p.asIdeal = maximalIdeal R := fun p =>
    le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
      (hmem.2 ⟨p.isPrime, bot_le⟩ (IsLocalRing.le_maximalIdeal p.isPrime.ne_top))
  have : Subsingleton (PrimeSpectrum R) :=
    ⟨fun p q => PrimeSpectrum.ext ((hall p).trans (hall q).symm)⟩
  have heq : ringKrullDim R = 0 := by
    rw [ringKrullDim]
    have : Nonempty (PrimeSpectrum R) := ⟨⟨maximalIdeal R, inferInstance⟩⟩
    let : Unique (PrimeSpectrum R) := uniqueOfSubsingleton (Classical.arbitrary _)
    exact Order.krullDim_eq_zero_of_unique
  rw [heq] at hdim
  exact hdim.false

theorem exists_parameter_notMem_minimalPrimes
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ∉ (maximalIdeal R) ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p :=
  open IsRegularLocalRing_isDomain.W2RLR.No4PatchingCore renaming
    exists_parameter_notMem_minimalPrimes → sharedProof in
  sharedProof R hdim

end PrimeAvoidance

section DimensionDrop

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

theorem annihilator_self_eq_bot (R : Type u) [CommRing R] : Module.annihilator R R = ⊥ :=
  Module.annihilator_eq_bot.mpr (inferInstance : FaithfulSMul R R)

theorem ringKrullDim_quotSMulTop_succ_eq_of_forall_notMem_minimalPrimes
    {x : R} (hx : x ∈ maximalIdeal R) (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ringKrullDim (QuotSMulTop x R) + 1 = ringKrullDim R :=
  IsLocalRing.ringKrullDim_quotSMulTop_add_one_of_forall_minimalPrimes_notMem hx hxmin

theorem ringKrullDim_quotient_span_singleton_succ_eq_of_forall_notMem_minimalPrimes
    {x : R} (hx : x ∈ maximalIdeal R) (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R :=
  IsLocalRing.ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem
    hx hxmin

end DimensionDrop

section QuotientRegularity

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

theorem isRegularLocalRing_quotient_span_singleton_of_forall_notMem_minimalPrimes
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) [IsLocalRing (R ⧸ Ideal.span {x})] :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 =
        (maximalIdeal R).spanFinrank :=
  open IsRegularLocalRing_isDomain.W2RLR.No4PatchingCore renaming
    isRegularLocalRing_quotient_span_singleton_of_forall_notMem_minimalPrimes →
      quotientRegularity in
  quotientRegularity R hx hx2 hxmin

end QuotientRegularity

section MatsumuraDomain

theorem isDomain_of_isRegularLocalRing_aux :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = n → IsDomain R :=
  fun _ R _ _ _ => _root_.IsRegularLocalRing.isDomain R

theorem isDomain_of_isRegularLocalRing (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R :=
  isDomain_of_isRegularLocalRing_aux ((maximalIdeal R).spanFinrank) R rfl

end MatsumuraDomain

end No4PatchingCore

end W2RLR

open IsLocalRing

theorem
  _root_.IsRegularLocalRing.quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
    (R : Type*) [CommRing R] [IsRegularLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) [IsLocalRing (R ⧸ Ideal.span {x})] :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 = (maximalIdeal R).spanFinrank :=
  W2RLR.No4PatchingCore.isRegularLocalRing_quotient_span_singleton_of_forall_notMem_minimalPrimes R
    hx hx2 hxmin
end IsRegularLocalRing_quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
