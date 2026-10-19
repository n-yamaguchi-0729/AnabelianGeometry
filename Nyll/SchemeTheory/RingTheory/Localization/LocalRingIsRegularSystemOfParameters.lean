/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalRing_isRegular_of_systemOfParameters.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Earlier source notices recorded for the cited upstream material:
Copyright (c) 2025 Andrew Yang. All rights reserved.
Authors: Andrew Yang, Kevin Buzzard, Michael Rothgang
https://github.com/ImperialCollegeLondon/FLT/blob/a7dbce8494c29858093974a612a72b6454fc5cba/FLT/Patching/Utils/Depth.lean

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.RingTheory.RegularLocal.ModuleDepthRegularQuotient
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Regular systems of parameters in Cohen–Macaulay local rings

The depth and associated-prime bounds come from the common module-depth proofs.
The arguments below establish regularity of a system of parameters by induction.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsLocalRing_isRegular_of_systemOfParameters

open IsLocalRing RingTheory

namespace Ws14Port

universe u

open AlgebraicCurves.Foundations.Algebra.Proofs.Module_depth_quotSMulTop_succ_eq.Ws14Port

section

open _root_.Module.IsLocalRing
open _root_.Submodule
open _root_.Pointwise

noncomputable section

namespace IsLocalRing
open _root_.Module.IsLocalRing

/-- The unmixedness assertion that every associated-prime quotient of a Cohen-Macaulay local
ring has its full Krull dimension. -/
def CMUnmixednessHypothesis : Prop :=
  ∀ (S : Type u) [CommRing S] [IsLocalRing S] [IsNoetherianRing S],
    (.some (Module.depth S S) : WithBot ℕ∞) = ringKrullDim S →
    ∀ p ∈ associatedPrimes S S, ringKrullDim (S ⧸ p) = ringKrullDim S

theorem cmUnmixednessHypothesis_of_depth_le_dim
    (h : ∀ (S : Type u) [CommRing S] [IsLocalRing S] [IsNoetherianRing S],
      ∀ p ∈ associatedPrimes S S,
        (.some (Module.depth S S) : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ p)) :
    CMUnmixednessHypothesis.{u} := by
  intro S _ _ _ hCM p hp
  refine le_antisymm (ringKrullDim_quotient_le p) ?_
  calc ringKrullDim S = (.some (Module.depth S S) : WithBot ℕ∞) := hCM.symm
    _ ≤ ringKrullDim (S ⧸ p) := h S p hp

theorem isAssociatedPrime_eq_bot_of_isDomain {S : Type u} [CommRing S] [IsDomain S]
    [IsNoetherianRing S] {p : Ideal S} (hp : IsAssociatedPrime p S) : p = ⊥ := by
  obtain ⟨hprime, y, hy⟩ := isAssociatedPrime_iff.mp hp
  rcases eq_or_ne y 0 with rfl | hy0
  · exfalso
    apply hprime.ne_top
    rw [hy, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem ⊥
  · rw [hy, eq_bot_iff]
    intro r hr
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] at hr
    rw [Submodule.mem_bot]
    rcases mul_eq_zero.mp hr with h | h
    · exact h
    · exact absurd h hy0

theorem unmixedness_of_isDomain (S : Type u) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [IsDomain S] :
    ∀ p ∈ associatedPrimes S S, ringKrullDim (S ⧸ p) = ringKrullDim S := by
  intro p hp
  obtain rfl := isAssociatedPrime_eq_bot_of_isDomain hp
  exact ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot S)

theorem depth_le_ringKrullDim_quotient_of_isDomain (S : Type u) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [IsDomain S] :
    ∀ p ∈ associatedPrimes S S,
      (.some (Module.depth S S) : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ p) := by
  intro p hp
  obtain rfl := isAssociatedPrime_eq_bot_of_isDomain hp
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot S)]
  exact Module.depth_le_dim S S

theorem exists_ringKrullDim_eq_natCast (S : Type u) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] :
    ∃ m : ℕ, ringKrullDim S = (m : WithBot ℕ∞) := by
  cases hk : ringKrullDim S with
  | bot => exact absurd hk ringKrullDim_ne_bot
  | coe e =>
    cases e with
    | top => exact absurd hk ringKrullDim_ne_top
    | coe m => exact ⟨m, by norm_cast⟩

theorem eq_maximalIdeal_of_ringKrullDim_quotient_le_zero {R : Type u} [CommRing R]
    [IsLocalRing R] {p : Ideal R} [p.IsPrime]
    (h : ringKrullDim (R ⧸ p) ≤ 0) : p = maximalIdeal R := by
  have : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have : Ring.KrullDimLE 0 (R ⧸ p) := Ring.krullDimLE_iff.mpr (by exact_mod_cast h)
  have hfield : IsField (R ⧸ p) := Ring.KrullDimLE.isField_of_isDomain
  exact IsLocalRing.eq_maximalIdeal
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient p).mpr hfield)

theorem notMem_of_ringKrullDim_quotient_cons_le_zero {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x : R} {rest : List R}
    (hmem : ∀ y ∈ x :: rest, y ∈ maximalIdeal R)
    (hsop : ringKrullDim (R ⧸ Ideal.ofList (x :: rest)) ≤ 0)
    {p : Ideal R} (hp : p.IsPrime)
    (hpdim : ringKrullDim (R ⧸ p) = ringKrullDim R)
    (hlen : ((rest.length : ℕ) : WithBot ℕ∞) < ringKrullDim R) :
    x ∉ p := by
  classical
  intro hxp
  have : p.IsPrime := hp
  have : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk p) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  set s : Set (R ⧸ p) := {y | y ∈ rest.map (Ideal.Quotient.mk p)} with hs_def
  have hjac : s ⊆ Ring.jacobson (R ⧸ p) := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    rintro y' hy'
    rw [hs_def, Set.mem_ofPred_eq, List.mem_map] at hy'
    obtain ⟨y, hy, rfl⟩ := hy'
    intro hu
    exact hmem y (List.mem_cons_of_mem x hy) (IsLocalHom.map_nonunit y hu)
  have hcount := ringKrullDim_le_ringKrullDim_quotient_add_encard s hjac
  have hspan : Ideal.span s = Ideal.map (Ideal.Quotient.mk p) (Ideal.ofList rest) := by
    rw [Ideal.map_ofList]
  have hsup : Ideal.ofList (x :: rest) ≤ p ⊔ Ideal.ofList rest := by
    rw [Ideal.ofList_cons]
    exact sup_le_sup_right (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxp)) _
  have hdq : ringKrullDim ((R ⧸ p) ⧸ Ideal.span s) ≤ 0 := by
    rw [hspan, ringKrullDim_eq_of_ringEquiv
      (DoubleQuot.quotQuotEquivQuotSup p (Ideal.ofList rest))]
    calc ringKrullDim (R ⧸ (p ⊔ Ideal.ofList rest))
        ≤ ringKrullDim (R ⧸ Ideal.ofList (x :: rest)) :=
          ringKrullDim_le_of_surjective (Ideal.Quotient.factor hsup)
            (Ideal.Quotient.factor_surjective hsup)
      _ ≤ 0 := hsop
  have hcard : s.encard ≤ (rest.length : ℕ∞) := by
    rw [hs_def]
    calc ({y | y ∈ rest.map (Ideal.Quotient.mk p)} : Set (R ⧸ p)).encard
        = (((rest.map (Ideal.Quotient.mk p)).toFinset : Set (R ⧸ p))).encard := by
          rw [List.coe_toFinset]
      _ = ((rest.map (Ideal.Quotient.mk p)).toFinset.card : ℕ∞) :=
          Set.encard_coe_eq_coe_finsetCard _
      _ ≤ ((rest.map (Ideal.Quotient.mk p)).length : ℕ∞) := by
          exact_mod_cast List.toFinset_card_le (rest.map (Ideal.Quotient.mk p))
      _ = (rest.length : ℕ∞) := by rw [List.length_map]
  rw [hpdim] at hcount
  have hfinal : ringKrullDim R ≤ ((rest.length : ℕ) : WithBot ℕ∞) := by
    refine hcount.trans ?_
    calc ringKrullDim ((R ⧸ p) ⧸ Ideal.span s) + (s.encard : WithBot ℕ∞)
        ≤ 0 + (((rest.length : ℕ) : ℕ∞) : WithBot ℕ∞) := by
          refine add_le_add hdq ?_
          exact_mod_cast hcard
      _ = ((rest.length : ℕ) : WithBot ℕ∞) := by
          rw [zero_add]
          norm_cast
  exact absurd hfinal (not_le.mpr hlen)

theorem isRegular_of_sop_of_cmUnmixedness (hunmix : CMUnmixednessHypothesis.{u}) :
    ∀ (d : ℕ) (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      (.some (Module.depth R R) : WithBot ℕ∞) = ringKrullDim R →
      ringKrullDim R = (d : WithBot ℕ∞) →
      ∀ xs : List R, xs.length = d →
        (∀ y ∈ xs, y ∈ maximalIdeal R) →
        ringKrullDim (R ⧸ Ideal.ofList xs) = 0 →
        Sequence.IsRegular R xs := by
  intro d
  induction d with
  | zero =>
    intro R _ _ _ hCM hdim xs hlen hmem hsop
    cases xs with
    | nil => exact Sequence.IsRegular.nil R R
    | cons x rest =>
        have : rest.length + 1 = 0 := hlen
        omega
  | succ n IH =>
    intro R _ _ _ hCM hdim xs hlen hmem hsop
    cases xs with
    | nil =>
        have : 0 = n + 1 := hlen
        omega
    | cons x rest =>
    have hrestlen : rest.length = n := Nat.succ.inj hlen
    have hxm : x ∈ maximalIdeal R := hmem x (List.mem_cons.mpr (Or.inl rfl))
    have hdepth : Module.depth R R = ((n + 1 : ℕ) : ℕ∞) := by
      have h := hCM.trans hdim
      exact_mod_cast h
    have hxreg : IsSMulRegular R x := by
      by_contra hcon
      have hx_in : x ∈ {r : R | IsSMulRegular R r}ᶜ := hcon
      rw [← biUnion_associatedPrimes_eq_compl_regular R R] at hx_in
      simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hx_in
      obtain ⟨p, hpass, hxp⟩ := hx_in
      have hpprime : p.IsPrime := hpass.isPrime
      have hpdim : ringKrullDim (R ⧸ p) = ringKrullDim R := hunmix R hCM p hpass
      refine (notMem_of_ringKrullDim_quotient_cons_le_zero hmem (le_of_eq hsop) hpprime hpdim
        ?_) hxp
      rw [hdim, hrestlen]
      exact_mod_cast Nat.lt_succ_self n
    have hloc' : IsLocalRing (R ⧸ Ideal.span {x}) :=
      Module.isLocalRing_quotient_span_singleton hxm
    have hdim' : ringKrullDim (R ⧸ Ideal.span {x}) = ((n : ℕ) : WithBot ℕ∞) :=
      Module.ringKrullDim_quotient_span_singleton_of_ringKrullDim_eq R hxreg hxm
        (by rw [hdim])
    have hsub : (Ideal.span {x} : Submodule R R) = x • (⊤ : Submodule R R) := by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
    have hdepth' : Module.depth (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x}) = ((n : ℕ) : ℕ∞) := by
      have h1 : Module.depth (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x}) =
          Module.depth R (R ⧸ Ideal.span {x}) :=
        Module.depth_quotient_eq_depth (Ideal.span {x}) (R ⧸ Ideal.span {x})
      have h2 : Module.depth R (R ⧸ Ideal.span {x}) = Module.depth R (QuotSMulTop x R) :=
        Module.depth_eq_of_linearEquiv (Submodule.quotEquivOfEq _ _ hsub)
      have h3 := Module.depth_quotSMulTop_succ_eq R hxm hxreg
      rw [hdepth] at h3
      rw [h1, h2]
      have hcast : ((n + 1 : ℕ) : ℕ∞) = ((n : ℕ) : ℕ∞) + 1 := by push_cast; ring
      rw [hcast] at h3
      exact WithTop.add_right_cancel ENat.one_ne_top h3
    have hCM' : (.some (Module.depth (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) :
        WithBot ℕ∞) = ringKrullDim (R ⧸ Ideal.span {x}) := by
      rw [hdepth', hdim']
      rfl
    have hlen' : (rest.map (Ideal.Quotient.mk (Ideal.span {x}))).length = n := by
      rw [List.length_map]; exact hrestlen
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hmem' : ∀ y ∈ rest.map (Ideal.Quotient.mk (Ideal.span {x})),
        y ∈ maximalIdeal (R ⧸ Ideal.span {x}) := by
      intro y' hy'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hy'
      intro hu
      exact hmem y (List.mem_cons_of_mem x hy) (IsLocalHom.map_nonunit y hu)
    have hsop' : ringKrullDim ((R ⧸ Ideal.span {x}) ⧸
        Ideal.ofList (rest.map (Ideal.Quotient.mk (Ideal.span {x})))) = 0 := by
      have hofl : Ideal.ofList (rest.map (Ideal.Quotient.mk (Ideal.span {x}))) =
          Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (Ideal.ofList rest) :=
        (Ideal.map_ofList _ _).symm
      rw [hofl, ringKrullDim_eq_of_ringEquiv
        (DoubleQuot.quotQuotEquivQuotSup (Ideal.span {x}) (Ideal.ofList rest))]
      rw [show Ideal.span {x} ⊔ Ideal.ofList rest = Ideal.ofList (x :: rest) from
        (Ideal.ofList_cons x rest).symm]
      exact hsop
    have hIH := IH (R ⧸ Ideal.span {x}) hCM' hdim'
      (rest.map (Ideal.Quotient.mk (Ideal.span {x}))) hlen' hmem' hsop'
    refine Sequence.IsRegular.cons' hxreg ?_
    have e' : (R ⧸ Ideal.span {x}) ≃ₗ[R ⧸ Ideal.span {x}] QuotSMulTop x R :=
      LinearEquiv.extendScalarsOfSurjective
        (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)
        (Submodule.quotEquivOfEq _ _ hsub)
    exact (LinearEquiv.isRegular_congr e' _).mp hIH

private theorem isRegular_of_sop {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hunmix : CMUnmixednessHypothesis.{u}) {d : ℕ}
    (hCM : (.some (Module.depth R R) : WithBot ℕ∞) = ringKrullDim R)
    (hdim : ringKrullDim R = (d : WithBot ℕ∞))
    (xs : List R) (hlen : xs.length = d)
    (hmem : ∀ y ∈ xs, y ∈ maximalIdeal R)
    (hsop : ringKrullDim (R ⧸ Ideal.ofList xs) = 0) :
    Sequence.IsRegular R xs :=
  isRegular_of_sop_of_cmUnmixedness hunmix d R hCM hdim xs hlen hmem hsop

theorem IsCohenMacaulayOfDim.isRegular_of_sop {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {d : ℕ} (hCM : IsCohenMacaulayOfDim R d)
    (hunmix : CMUnmixednessHypothesis.{u})
    (xs : List R) (hlen : xs.length = d)
    (hmem : ∀ y ∈ xs, y ∈ maximalIdeal R)
    (hsop : ringKrullDim (R ⧸ Ideal.ofList xs) = 0) :
    Sequence.IsRegular R xs :=
  isRegular_of_sop_of_cmUnmixedness hunmix d R
    (by rw [hCM.depth_eq, hCM.ringKrullDim_eq]; rfl)
    hCM.ringKrullDim_eq xs hlen hmem hsop

theorem isRegular_of_sop_of_ringKrullDim_eq_zero {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (_hdim : ringKrullDim R = (0 : WithBot ℕ∞))
    (xs : List R) (hlen : xs.length = 0) :
    Sequence.IsRegular R xs := by
  cases xs with
  | nil => exact Sequence.IsRegular.nil R R
  | cons x rest =>
      have : rest.length + 1 = 0 := hlen
      omega

theorem isRegular_of_sop_of_ringKrullDim_eq_one {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hCM : (.some (Module.depth R R) : WithBot ℕ∞) = ringKrullDim R)
    (hdim : ringKrullDim R = ((1 : ℕ) : WithBot ℕ∞))
    (xs : List R) (hlen : xs.length = 1)
    (hmem : ∀ y ∈ xs, y ∈ maximalIdeal R)
    (hsop : ringKrullDim (R ⧸ Ideal.ofList xs) = 0) :
    Sequence.IsRegular R xs := by
  obtain ⟨x, rfl⟩ : ∃ x, xs = [x] := by
    cases xs with
    | nil =>
        have : (0 : ℕ) = 1 := hlen
        omega
    | cons x rest =>
      cases rest with
      | nil => exact ⟨x, rfl⟩
      | cons y t =>
          have : t.length + 1 + 1 = 1 := hlen
          omega
  have hxm : x ∈ maximalIdeal R := hmem x (List.mem_singleton.mpr rfl)
  have hdepth : Module.depth R R = ((1 : ℕ) : ℕ∞) := by
    have h := hCM.trans hdim
    exact_mod_cast h
  have hmnotass : ¬ IsAssociatedPrime (maximalIdeal R) R := by
    obtain ⟨s, hs, hs', hslen⟩ := Module.exists_isWeaklyRegular_of_le_depth R 1
      (le_of_eq hdepth.symm)
    obtain ⟨y, rfl⟩ : ∃ y, s = [y] := by
      cases s with
      | nil =>
          have : (0 : ℕ) = 1 := hslen
          omega
      | cons y t =>
        cases t with
        | nil => exact ⟨y, rfl⟩
        | cons z u =>
            have : u.length + 1 + 1 = 1 := hslen
            omega
    have hyreg : IsSMulRegular R y := (Sequence.isWeaklyRegular_singleton_iff R y).mp hs
    exact Module.not_isAssociatedPrime_maximalIdeal_of_isSMulRegular
      (hs' y (List.mem_singleton.mpr rfl)) hyreg
  have hxreg : IsSMulRegular R x := by
    by_contra hcon
    have hx_in : x ∈ {r : R | IsSMulRegular R r}ᶜ := hcon
    rw [← biUnion_associatedPrimes_eq_compl_regular R R] at hx_in
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hx_in
    obtain ⟨p, hpass, hxp⟩ := hx_in
    have hpprime : p.IsPrime := hpass.isPrime
    have : p.IsPrime := hpprime
    by_cases hpm : p = maximalIdeal R
    · exact hmnotass (hpm ▸ hpass)
    · have hpdim : ringKrullDim (R ⧸ p) = ringKrullDim R := by
        have : IsLocalRing (R ⧸ p) :=
          IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
        obtain ⟨m, hm⟩ := exists_ringKrullDim_eq_natCast (R ⧸ p)
        have hle : ringKrullDim (R ⧸ p) ≤ ringKrullDim R := ringKrullDim_quotient_le p
        rw [hm, hdim] at hle ⊢
        have hm1 : m ≤ 1 := by exact_mod_cast hle
        have hm0 : m ≠ 0 := by
          intro h0
          exact hpm (eq_maximalIdeal_of_ringKrullDim_quotient_le_zero
            (by rw [hm, h0]; norm_cast))
        have : m = 1 := by omega
        rw [this]
      refine (notMem_of_ringKrullDim_quotient_cons_le_zero (rest := []) hmem (le_of_eq hsop)
        hpprime hpdim ?_) hxp
      rw [hdim]
      simp only [List.length_nil, Nat.cast_zero]
      exact_mod_cast Nat.zero_lt_one
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem]
  exact (Sequence.isWeaklyRegular_singleton_iff R x).mpr hxreg

end IsLocalRing
end

end

section

open _root_.Module.IsLocalRing
open _root_.Submodule
open _root_.Pointwise

noncomputable section

namespace IsLocalRing
open _root_.Module.IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem ne_top_of_radical_eq_maximalIdeal {I : Ideal R}
    (hrad : I.radical = maximalIdeal R) : I ≠ ⊤ := by
  intro h
  apply (maximalIdeal.isMaximal R).ne_top
  rw [← hrad, Ideal.radical_eq_top]
  exact h

theorem isPrime_quotient_eq_map_maximalIdeal_of_radical_eq_maximalIdeal {I : Ideal R}
    (hrad : I.radical = maximalIdeal R) (P : Ideal (R ⧸ I)) (hP : P.IsPrime) :
    P = Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) := by
  have := hP
  have hcomap_prime : (Ideal.comap (Ideal.Quotient.mk I) P).IsPrime :=
    Ideal.IsPrime.comap (Ideal.Quotient.mk I)
  have hIle : I ≤ Ideal.comap (Ideal.Quotient.mk I) P := by
    have h : RingHom.ker (Ideal.Quotient.mk I) ≤ Ideal.comap (Ideal.Quotient.mk I) P :=
      Ideal.ker_le_comap (Ideal.Quotient.mk I)
    rwa [Ideal.mk_ker] at h
  have h1 : maximalIdeal R ≤ Ideal.comap (Ideal.Quotient.mk I) P := by
    rw [← hrad]
    exact hcomap_prime.radical_le_iff.mpr hIle
  have h2 : Ideal.comap (Ideal.Quotient.mk I) P ≤ maximalIdeal R :=
    le_maximalIdeal hcomap_prime.ne_top
  rw [← le_antisymm h2 h1,
    Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective P]

theorem ringKrullDim_quotient_eq_zero_of_radical_eq_maximalIdeal {I : Ideal R}
    (hrad : I.radical = maximalIdeal R) :
    ringKrullDim (R ⧸ I) = 0 := by
  have hne : I ≠ ⊤ := ne_top_of_radical_eq_maximalIdeal hrad
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have huniq : ∃! P : Ideal (R ⧸ I), P.IsPrime :=
    ⟨maximalIdeal (R ⧸ I), (maximalIdeal.isMaximal _).isPrime, fun P hP =>
      (isPrime_quotient_eq_map_maximalIdeal_of_radical_eq_maximalIdeal hrad P hP).trans
        (isPrime_quotient_eq_map_maximalIdeal_of_radical_eq_maximalIdeal hrad _
          (maximalIdeal.isMaximal _).isPrime).symm⟩
  have : Ring.KrullDimLE 0 (R ⧸ I) :=
    (((Ring.krullDimLE_zero_and_isLocalRing_tfae (R ⧸ I)).out 2 1 rfl rfl).mp huniq).1
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

theorem eq_maximalIdeal_of_isPrime_of_le_of_ringKrullDim_quotient_le_zero {I p : Ideal R}
    (hdim : ringKrullDim (R ⧸ I) ≤ 0) (hp : p.IsPrime) (hIp : I ≤ p) :
    p = maximalIdeal R := by
  have := hp
  refine eq_maximalIdeal_of_ringKrullDim_quotient_le_zero ?_
  calc ringKrullDim (R ⧸ p)
      ≤ ringKrullDim (R ⧸ I) :=
        ringKrullDim_le_of_surjective (Ideal.Quotient.factor hIp)
          (Ideal.Quotient.factor_surjective hIp)
    _ ≤ 0 := hdim

theorem radical_eq_maximalIdeal_of_ringKrullDim_quotient_eq_zero {I : Ideal R}
    (hne : I ≠ ⊤) (hdim : ringKrullDim (R ⧸ I) = 0) :
    I.radical = maximalIdeal R := by
  rw [Ideal.radical_eq_sInf]
  apply le_antisymm
  · exact sInf_le ⟨le_maximalIdeal hne, (maximalIdeal.isMaximal R).isPrime⟩
  · refine le_sInf ?_
    rintro p ⟨hIp, hp⟩
    exact (eq_maximalIdeal_of_isPrime_of_le_of_ringKrullDim_quotient_le_zero
      (le_of_eq hdim) hp hIp).ge

theorem radical_eq_maximalIdeal_iff_ne_top_and_ringKrullDim_quotient_eq_zero (I : Ideal R) :
    I.radical = maximalIdeal R ↔ (I ≠ ⊤ ∧ ringKrullDim (R ⧸ I) = 0) :=
  ⟨fun hrad => ⟨ne_top_of_radical_eq_maximalIdeal hrad,
      ringKrullDim_quotient_eq_zero_of_radical_eq_maximalIdeal hrad⟩,
    fun ⟨hne, hdim⟩ => radical_eq_maximalIdeal_of_ringKrullDim_quotient_eq_zero hne hdim⟩

theorem radical_eq_maximalIdeal_iff_ne_top_and_ringKrullDim_quotient_eq_zero_of_noetherian
    [IsNoetherianRing R] (I : Ideal R) :
    I.radical = IsLocalRing.maximalIdeal R ↔ (I ≠ ⊤ ∧ ringKrullDim (R ⧸ I) = 0) :=
  radical_eq_maximalIdeal_iff_ne_top_and_ringKrullDim_quotient_eq_zero I

theorem ofList_ne_top_of_forall_mem_maximalIdeal {xs : List R}
    (hmem : ∀ x ∈ xs, x ∈ maximalIdeal R) :
    Ideal.ofList xs ≠ ⊤ :=
  ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
    (Ideal.span_le.mpr fun x hx => hmem x hx)

theorem ofList_radical_eq_maximalIdeal_iff_ringKrullDim_quotient_eq_zero {xs : List R}
    (hmem : ∀ x ∈ xs, x ∈ maximalIdeal R) :
    (Ideal.ofList xs).radical = maximalIdeal R ↔
      ringKrullDim (R ⧸ Ideal.ofList xs) = 0 := by
  rw [radical_eq_maximalIdeal_iff_ne_top_and_ringKrullDim_quotient_eq_zero]
  exact and_iff_right (ofList_ne_top_of_forall_mem_maximalIdeal hmem)

/-- The regular-sequence assertion for a parameter list of the Cohen-Macaulay dimension whose
generated ideal has maximal-ideal radical. -/
def matsumuraThm174iiiSopRegularRowRadicalForm (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : Prop :=
  ∀ (d : ℕ) (xs : List R),
    IsCohenMacaulayOfDim R d →
    xs.length = d →
    (∀ x ∈ xs, x ∈ maximalIdeal R) →
    (Ideal.ofList xs).radical = maximalIdeal R →
    Sequence.IsRegular R xs

/-- The regular-sequence assertion for a parameter list of the Cohen-Macaulay dimension whose
generated ideal gives a zero-dimensional quotient. -/
def matsumuraThm174iiiSopRegularRowQuotientDimForm (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : Prop :=
  ∀ (d : ℕ) (xs : List R),
    IsCohenMacaulayOfDim R d →
    xs.length = d →
    (∀ x ∈ xs, x ∈ maximalIdeal R) →
    ringKrullDim (R ⧸ Ideal.ofList xs) = 0 →
    Sequence.IsRegular R xs

theorem matsumuraThm174iiiSopRegularRow_radicalForm_iff_quotientDimForm
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    matsumuraThm174iiiSopRegularRowRadicalForm R ↔
      matsumuraThm174iiiSopRegularRowQuotientDimForm R := by
  constructor
  · intro hrow d xs hCM hlen hmem hdim
    exact hrow d xs hCM hlen hmem
      ((ofList_radical_eq_maximalIdeal_iff_ringKrullDim_quotient_eq_zero hmem).mpr hdim)
  · intro hrow d xs hCM hlen hmem hrad
    exact hrow d xs hCM hlen hmem
      ((ofList_radical_eq_maximalIdeal_iff_ringKrullDim_quotient_eq_zero hmem).mp hrad)

theorem matsumuraThm174iiiSopRegularRowQuotientDimForm_of_cmUnmixedness
    (hunmix : CMUnmixednessHypothesis.{u}) (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    matsumuraThm174iiiSopRegularRowQuotientDimForm R :=
  fun _d xs hCM hlen hmem hsop => IsCohenMacaulayOfDim.isRegular_of_sop hCM hunmix xs hlen hmem hsop

theorem matsumuraThm174iiiSopRegularRowRadicalForm_of_cmUnmixedness
    (hunmix : CMUnmixednessHypothesis.{u}) (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    matsumuraThm174iiiSopRegularRowRadicalForm R :=
  (matsumuraThm174iiiSopRegularRow_radicalForm_iff_quotientDimForm R).mpr
    (matsumuraThm174iiiSopRegularRowQuotientDimForm_of_cmUnmixedness hunmix R)

theorem IsCohenMacaulayOfDim.isRegular_of_sop_radical {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {d : ℕ} (hCM : IsCohenMacaulayOfDim R d)
    (hunmix : CMUnmixednessHypothesis.{u})
    (xs : List R) (hlen : xs.length = d)
    (hmem : ∀ y ∈ xs, y ∈ maximalIdeal R)
    (hrad : (Ideal.ofList xs).radical = maximalIdeal R) :
    Sequence.IsRegular R xs :=
  IsCohenMacaulayOfDim.isRegular_of_sop hCM hunmix xs hlen hmem
    ((ofList_radical_eq_maximalIdeal_iff_ringKrullDim_quotient_eq_zero hmem).mp hrad)

theorem isRegular_of_sop_radical_of_ringKrullDim_eq_one {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hCM : (.some (Module.depth R R) : WithBot ℕ∞) = ringKrullDim R)
    (hdim : ringKrullDim R = ((1 : ℕ) : WithBot ℕ∞))
    (xs : List R) (hlen : xs.length = 1)
    (hmem : ∀ y ∈ xs, y ∈ maximalIdeal R)
    (hrad : (Ideal.ofList xs).radical = maximalIdeal R) :
    Sequence.IsRegular R xs :=
  isRegular_of_sop_of_ringKrullDim_eq_one hCM hdim xs hlen hmem
    ((ofList_radical_eq_maximalIdeal_iff_ringKrullDim_quotient_eq_zero hmem).mp hrad)

theorem cmUnmixednessHypothesis_holds : CMUnmixednessHypothesis.{u} := by
  refine cmUnmixednessHypothesis_of_depth_le_dim ?_
  intro S _ _ _ p hp
  exact Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes S hp

theorem matsumuraThm174iiiSopRegularRowQuotientDimForm_holds (R : Type u) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] :
    matsumuraThm174iiiSopRegularRowQuotientDimForm R :=
  matsumuraThm174iiiSopRegularRowQuotientDimForm_of_cmUnmixedness
    cmUnmixednessHypothesis_holds R

theorem matsumuraThm174iiiSopRegularRowRadicalForm_holds (R : Type u) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] :
    matsumuraThm174iiiSopRegularRowRadicalForm R :=
  matsumuraThm174iiiSopRegularRowRadicalForm_of_cmUnmixedness cmUnmixednessHypothesis_holds R

theorem IsCohenMacaulayOfDim.isRegular_of_sop_unconditional {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {d : ℕ} (hCM : IsCohenMacaulayOfDim R d)
    (xs : List R) (hlen : xs.length = d)
    (hmem : ∀ y ∈ xs, y ∈ maximalIdeal R)
    (hsop : ringKrullDim (R ⧸ Ideal.ofList xs) = 0) :
    Sequence.IsRegular R xs :=
  IsCohenMacaulayOfDim.isRegular_of_sop hCM cmUnmixednessHypothesis_holds xs hlen hmem hsop

theorem IsCohenMacaulayOfDim.isRegular_of_sop_radical_unconditional {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {d : ℕ} (hCM : IsCohenMacaulayOfDim R d)
    (xs : List R) (hlen : xs.length = d)
    (hmem : ∀ y ∈ xs, y ∈ maximalIdeal R)
    (hrad : (Ideal.ofList xs).radical = maximalIdeal R) :
    Sequence.IsRegular R xs :=
  IsCohenMacaulayOfDim.isRegular_of_sop_radical hCM cmUnmixednessHypothesis_holds xs hlen hmem hrad

end IsLocalRing
end

end

end Ws14Port

theorem _root_.IsLocalRing.isRegular_of_systemOfParameters
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hCM : (Module.depth R R : WithBot ℕ∞) = ringKrullDim R)
    {d : ℕ} (hdim : ringKrullDim R = d)
    (xs : List R) (hlen : xs.length = d) (hmem : ∀ y ∈ xs, y ∈ maximalIdeal R)
    (hsop : ringKrullDim (R ⧸ Ideal.ofList xs) = 0) :
    RingTheory.Sequence.IsRegular R xs :=
  Ws14Port.IsLocalRing.isRegular_of_sop_of_cmUnmixedness
    Ws14Port.IsLocalRing.cmUnmixednessHypothesis_holds d R hCM hdim xs hlen hmem hsop
end IsLocalRing_isRegular_of_systemOfParameters
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
