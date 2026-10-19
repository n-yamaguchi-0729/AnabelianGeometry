/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsIntegrallyClosed_mem_minimalPrimes_of_mem_associatedPrimes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.IntegrallyClosedDVRLocalization
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.IdealHeightEqOneDVRLocalizationAtPrime

/-!
# Is Integrally Closed height eq one of mem associated Primes
-/

section IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes

theorem _root_.IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    {x : B} (hx : x ≠ 0) (P : Ideal B) [P.IsPrime]
    (hP : P ∈ associatedPrimes B (B ⧸ Ideal.span {x})) : P.height = 1 :=
  Ideal.height_eq_one_of_isDiscreteValuationRing_localization_atPrime P
    (IsIntegrallyClosed.isDiscreteValuationRing_localization_of_mem_associatedPrimes hx P hP)
end IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

end IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes

section IsIntegrallyClosed_mem_minimalPrimes_of_mem_associatedPrimes

/-!
# Is Integrally Closed mem minimal Primes of mem associated Primes
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsIntegrallyClosed_mem_minimalPrimes_of_mem_associatedPrimes

theorem _root_.IsIntegrallyClosed.mem_minimalPrimes_of_mem_associatedPrimes
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    {x : A} (hx : x ≠ 0) (P : Ideal A) [P.IsPrime]
    (hP : P ∈ associatedPrimes A (A ⧸ Ideal.span {x})) : P ∈ (Ideal.span {x}).minimalPrimes := by
  have h1 : P.height = 1 := IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes hx P hP
  have hle : Ideal.span {x} ≤ P := by
    have h := (show IsAssociatedPrime P (A ⧸ Ideal.span {x}) from hP).annihilator_le
    rwa [Submodule.annihilator_top, Ideal.annihilator_quotient] at h
  have hbelow : ∀ q : Ideal A, q.IsPrime → q < P → q = ⊥ := by
    intro q hq hlt
    have := hq
    have hPle : P.height ≤ ((1 : ℕ) : ℕ∞) := by rw [h1]; norm_cast
    have hlt1 : q.height < ((1 : ℕ) : ℕ∞) := (Ideal.height_le_iff.mp hPle) q hq hlt
    have h0 : q.height = 0 := by
      apply Order.lt_one_iff.mp
      exact_mod_cast hlt1
    have hmin : q ∈ (⊥ : Ideal A).minimalPrimes := Ideal.height_eq_zero_iff.mp h0
    simpa [Ideal.minimalPrimes_eq_subsingleton_self] using hmin
  refine ⟨⟨‹P.IsPrime›, hle⟩, fun q hq hqP => ?_⟩
  rcases lt_or_eq_of_le hqP with hlt | rfl
  · exfalso
    have hqbot := hbelow q hq.1 hlt
    apply hx
    have hxq : x ∈ q := hq.2 (Ideal.subset_span rfl)
    simpa [hqbot] using hxq
  · exact le_rfl
end IsIntegrallyClosed_mem_minimalPrimes_of_mem_associatedPrimes
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

end IsIntegrallyClosed_mem_minimalPrimes_of_mem_associatedPrimes

section IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one

/-!
# Is Integrally Closed exists algebra Map eq of forall height eq one
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one

theorem _root_.IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (x : K)
    (hx : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      ∃ r s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K r) :
    ∃ r : R, algebraMap R K r = x := by
  classical
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R K b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb0
  by_cases hab : b ∣ a
  · obtain ⟨d, rfl⟩ := hab
    exact ⟨d, by rw [map_mul, mul_div_cancel_left₀ _ hbK]⟩
  exfalso
  have ha : Ideal.Quotient.mk (Ideal.span {b}) a ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ ha
  have := hp.isPrime
  have h1 : p.height = 1 := IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes hb0 p hp
  obtain ⟨r, s, hs, hrs⟩ := hx p h1
  have hsa : s * a = b * r := by
    apply IsFractionRing.injective R K
    rw [map_mul, map_mul, ← hrs]
    field_simp
  refine hs (hle ?_)
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
  exact ⟨r, hsa⟩
end IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

end IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one

section IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one

/-!
# Is Integrally Closed mem range algebra Map of forall height eq one
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one

theorem _root_.IsIntegrallyClosed.mem_range_algebraMap_of_forall_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (x : K)
    (hx : ∀ P : Ideal R, P.IsPrime → P.height = 1 →
      ∃ a s : R, s ∉ P ∧ x * algebraMap R K s = algebraMap R K a) :
    x ∈ Set.range (algebraMap R K) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hbK : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb0
  by_contra hnot
  have ha : a ∉ Ideal.span {b} := by
    intro hmem
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    exact hnot ⟨c, by rw [← hc, map_mul, mul_div_assoc, div_self hbK, mul_one]⟩
  have hcls : Ideal.Quotient.mk (Ideal.span {b}) a ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hcls
  have := hP.isPrime
  have hP1 : P.height = 1 := IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes hb0 P hP
  obtain ⟨a', s, hs, hxs⟩ := hx P hP.isPrime hP1
  apply hs
  apply hle
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  have hK : algebraMap R K (s * a) = algebraMap R K (a' * b) := by
    rw [map_mul, map_mul, ← hxs]
    field_simp
  have hR : s * a = a' * b := hinj hK
  exact Ideal.mem_span_singleton'.mpr ⟨a', hR.symm⟩
end IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

end IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one
