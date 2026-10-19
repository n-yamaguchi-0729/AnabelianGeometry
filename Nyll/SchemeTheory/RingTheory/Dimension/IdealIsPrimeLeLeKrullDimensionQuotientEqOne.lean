/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.RingTheory.IdealMemMemRadicalSpanSingletonIsPrime
import Nyll.SchemeTheory.RingTheory.Dimension.IdealHeightAddKrullDimensionQuotientEqKrullDimension

/-!
# Ideal exists is Prime le and le and ring Krull Dim quotient eq one
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one

universe u v

open Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula
  (ringKrullDim_quotient_radical_span_add_one exists_ringKrullDim_eq_natCast)

namespace P2mBertiniHyp

open _root_.Ideal _root_.Polynomial


theorem exists_isMaximal_ne (k : Type u) {A : Type v} [Field k] [CommRing A] [IsDomain A] [Algebra
  k A]
    [Algebra.FiniteType k A] (hA : 1 ≤ ringKrullDim A) (m : Ideal A) [hm : m.IsMaximal] :
    ∃ m' : Ideal A, m'.IsMaximal ∧ m' ≠ m := by
  by_contra! h
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  have hjac : (⊥ : Ideal A).jacobson = ⊥ :=
    IsJacobsonRing.out ‹_› Ideal.isRadical_bot
  have hle : m ≤ (⊥ : Ideal A).jacobson :=
    le_sInf fun J hJ => le_of_eq (h J hJ.2).symm
  rw [hjac, le_bot_iff] at hle
  subst hle
  have hF : IsField A := (Ring.isField_iff_maximal_bot).mpr hm
  have h0 := ringKrullDim_eq_zero_of_isField hF
  rw [h0] at hA
  exact absurd hA (by decide)

section Main

variable (k : Type u) [Field k] [IsAlgClosed k]

theorem step {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (hA : 2 ≤ ringKrullDim A) (m₀ m₁ : Ideal A) [m₀.IsMaximal] [m₁.IsMaximal] (hne : m₀ ≠ m₁) :
    ∃ P : Ideal A, P.IsPrime ∧ P ≤ m₀ ∧ P ≤ m₁ ∧ ringKrullDim (A ⧸ P) + 1 = ringKrullDim A := by
  obtain ⟨f, hf₀, hf₁, hf, hprime⟩ :=
    Ideal.exists_mem_and_mem_and_radical_span_singleton_isPrime k hA m₀ m₁ hne
  refine ⟨(Ideal.span {f}).radical, hprime, ?_, ?_,
    ringKrullDim_quotient_radical_span_add_one k m₀ hf hf₀⟩
  · exact (Ideal.IsPrime.radical_le_iff inferInstance).mpr
      ((Ideal.span_singleton_le_iff_mem _).mpr hf₀)
  · exact (Ideal.IsPrime.radical_le_iff inferInstance).mpr
      ((Ideal.span_singleton_le_iff_mem _).mpr hf₁)

theorem comap_mk_le {A : Type v} [CommRing A] {P' n : Ideal A} (h : P' ≤ n)
    {Q : Ideal (A ⧸ P')} (hQ : Q ≤ n.map (Ideal.Quotient.mk P')) :
    Q.comap (Ideal.Quotient.mk P') ≤ n := by
  calc Q.comap (Ideal.Quotient.mk P')
      ≤ (n.map (Ideal.Quotient.mk P')).comap (Ideal.Quotient.mk P') := Ideal.comap_mono hQ
    _ = n ⊔ Ideal.comap (Ideal.Quotient.mk P') ⊥ :=
        Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _
    _ = n := by
        refine sup_eq_left.mpr ?_
        rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
        exact h

theorem ringKrullDim_quotient_comap_mk {A : Type v} [CommRing A] (P' : Ideal A)
    (Q : Ideal (A ⧸ P')) :
    ringKrullDim (A ⧸ Q.comap (Ideal.Quotient.mk P')) = ringKrullDim ((A ⧸ P') ⧸ Q) := by
  let g : A →+* (A ⧸ P') ⧸ Q := (Ideal.Quotient.mk Q).comp (Ideal.Quotient.mk P')
  have hg : Function.Surjective g :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker g = Q.comap (Ideal.Quotient.mk P') := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
  rw [← hker]
  exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hg)

theorem main : ∀ (n : ℕ) {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k
  A],
    ringKrullDim A = n → 1 ≤ n → ∀ (m₀ m₁ : Ideal A) [m₀.IsMaximal] [m₁.IsMaximal],
      ∃ P : Ideal A, P.IsPrime ∧ P ≤ m₀ ∧ P ≤ m₁ ∧ ringKrullDim (A ⧸ P) = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ _ _ hdim hn m₀ m₁ _ _
  by_cases h1 : n = 1
  · subst h1
    refine ⟨⊥, Ideal.isPrime_bot, bot_le, bot_le, ?_⟩
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot A)]
    exact hdim
  have hn2 : 2 ≤ n := by omega
  have hA2 : (2 : WithBot ℕ∞) ≤ ringKrullDim A := by rw [hdim]; exact_mod_cast hn2
  have hA1 : (1 : WithBot ℕ∞) ≤ ringKrullDim A := le_trans (by decide) hA2
  have key : ∀ (n₀ n₁ : Ideal A) [n₀.IsMaximal] [n₁.IsMaximal], n₀ ≠ n₁ →
      ∃ P : Ideal A, P.IsPrime ∧ P ≤ n₀ ∧ P ≤ n₁ ∧ ringKrullDim (A ⧸ P) = 1 := by
    intro n₀ n₁ _ _ hne
    obtain ⟨P', hP', h0, h1', hdimP'⟩ := step k hA2 n₀ n₁ hne
    have := hP'
    have hq : ringKrullDim (A ⧸ P') = (n - 1 : ℕ) := by
      obtain ⟨d, hd⟩ := exists_ringKrullDim_eq_natCast k (A ⧸ P')
      rw [hdim, hd] at hdimP'
      have hdn : d + 1 = n := by exact_mod_cast hdimP'
      rw [hd]
      have : d = n - 1 := by omega
      rw [this]
    have hM0 : (n₀.map (Ideal.Quotient.mk P')).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact h0)
    have hM1 : (n₁.map (Ideal.Quotient.mk P')).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact h1')
    obtain ⟨Q, hQ, hQ0, hQ1, hQdim⟩ := ih (n - 1) (by omega) hq (by omega)
      (n₀.map (Ideal.Quotient.mk P')) (n₁.map (Ideal.Quotient.mk P'))
    have := hQ
    refine ⟨Q.comap (Ideal.Quotient.mk P'), Ideal.comap_isPrime _ Q, comap_mk_le h0 hQ0,
      comap_mk_le h1' hQ1, ?_⟩
    rw [ringKrullDim_quotient_comap_mk, hQdim]
  by_cases heq : m₀ = m₁
  · subst heq
    obtain ⟨m₂, hm₂, hne⟩ := exists_isMaximal_ne k hA1 m₀
    have := hm₂
    obtain ⟨P, hP, hP0, -, hd⟩ := key m₀ m₂ hne.symm
    exact ⟨P, hP, hP0, hP0, hd⟩
  · exact key m₀ m₁ heq

end Main

end P2mBertiniHyp

theorem _root_.Ideal.exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one
    (k : Type u) [Field k] [IsAlgClosed k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hA : 1 ≤ ringKrullDim A)
    (m₀ m₁ : Ideal A) [m₀.IsMaximal] [m₁.IsMaximal] :
    ∃ P : Ideal A, P.IsPrime ∧ P ≤ m₀ ∧ P ≤ m₁ ∧ ringKrullDim (A ⧸ P) = 1 := by
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast k A
  have h1 : 1 ≤ n := by
    rw [hn] at hA
    exact_mod_cast hA
  exact P2mBertiniHyp.main k n hn h1 m₀ m₁
end Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
