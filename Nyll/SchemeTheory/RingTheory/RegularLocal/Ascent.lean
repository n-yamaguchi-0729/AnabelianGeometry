/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Push
public import Nyll.SchemeTheory.RingTheory.Differentials.Basic
public import Nyll.SchemeTheory.RingTheory.Smooth.StandardSmoothFibreRegularity

/-! # Regular ascent and Frobenius independence -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_Mathlib_RingTheory_KmfloorsFiberPolynomialRegularAscent.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


universe u

open Polynomial

theorem kmf2_polyasc_isLocalization_primeCompl_congr {A : Type*} [CommSemiring A]
    {I J : Ideal A} [I.IsPrime] [J.IsPrime] (h : I = J)
    (S : Type*) [CommSemiring S] [Algebra A S]
    (hloc : IsLocalization I.primeCompl S) :
    IsLocalization J.primeCompl S := by
  subst h
  exact hloc

theorem kmf2_polyasc_isRegularLocalRing_of_isLocalization_primeCompl
    {A : Type*} [CommRing A] (J : Ideal A) [J.IsPrime]
    (S : Type*) [CommRing S] [Algebra A S]
    (h : IsLocalization J.primeCompl S)
    (hreg : IsRegularLocalRing (Localization.AtPrime J)) :
    IsRegularLocalRing S := by
  have : IsLocalization J.primeCompl S := h
  have : IsRegularLocalRing (Localization.AtPrime J) := hreg
  exact IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime J)
    (IsLocalization.algEquiv J.primeCompl (Localization.AtPrime J) S).toRingEquiv

theorem kmf2_polyasc_isRegularLocalRing_atPrime_of_isLocalization_primeCompl
    {A : Type*} [CommRing A] (J : Ideal A) [J.IsPrime]
    (S : Type*) [CommRing S] [Algebra A S]
    (h : IsLocalization J.primeCompl S)
    (hreg : IsRegularLocalRing S) :
    IsRegularLocalRing (Localization.AtPrime J) := by
  have : IsLocalization J.primeCompl S := h
  have : IsRegularLocalRing S := hreg
  exact IsRegularLocalRing.of_ringEquiv (R := S)
    (IsLocalization.algEquiv J.primeCompl S (Localization.AtPrime J)).toRingEquiv

theorem kmf2_polyasc_isRegularLocalRing_localization_atPrime_of_comap_C_eq_bot
    (D : Type u) [CommRing D] [IsDomain D]
    (Q : Ideal (Polynomial D)) [Q.IsPrime]
    (hQ0 : ∀ d : D, Polynomial.C d ∈ Q → d = 0) :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  let : Algebra (Polynomial D) (Polynomial (FractionRing D)) :=
    Polynomial.algebra D (FractionRing D)
  have hloc : IsLocalization
      ((nonZeroDivisors D).map (Polynomial.C : D →+* Polynomial D))
      (Polynomial (FractionRing D)) :=
    Polynomial.isLocalization (nonZeroDivisors D) (FractionRing D)
  have hdisj : Disjoint
      (((nonZeroDivisors D).map (Polynomial.C : D →+* Polynomial D) : Submonoid (Polynomial D)) :
        Set (Polynomial D)) (Q : Set (Polynomial D)) := by
    rw [Set.disjoint_left]
    intro x hx hxQ
    obtain ⟨d, hd, rfl⟩ := Submonoid.mem_map.mp hx
    exact mem_nonZeroDivisors_iff_ne_zero.mp hd (hQ0 d hxQ)
  have hq'' : (Q.map (algebraMap (Polynomial D) (Polynomial (FractionRing D)))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      ((nonZeroDivisors D).map (Polynomial.C : D →+* Polynomial D))
      (Polynomial (FractionRing D)) Q inferInstance hdisj
  have hcom : (Q.map (algebraMap (Polynomial D) (Polynomial (FractionRing D)))).comap
      (algebraMap (Polynomial D) (Polynomial (FractionRing D))) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint
      ((nonZeroDivisors D).map (Polynomial.C : D →+* Polynomial D))
      (Polynomial (FractionRing D)) inferInstance hdisj
  have htrans := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M := (nonZeroDivisors D).map (Polynomial.C : D →+* Polynomial D))
      (T := Localization.AtPrime
        (Q.map (algebraMap (Polynomial D) (Polynomial (FractionRing D)))))
      (p := Q.map (algebraMap (Polynomial D) (Polynomial (FractionRing D))))
  have hQloc : IsLocalization Q.primeCompl
      (Localization.AtPrime
        (Q.map (algebraMap (Polynomial D) (Polynomial (FractionRing D))))) :=
    kmf2_polyasc_isLocalization_primeCompl_congr hcom
      (Localization.AtPrime
        (Q.map (algebraMap (Polynomial D) (Polynomial (FractionRing D))))) htrans
  have hregq : IsRegularLocalRing
      (Localization.AtPrime
        (Q.map (algebraMap (Polynomial D) (Polynomial (FractionRing D))))) :=
    kmf2_fiber_isRegularLocalRing_localization_atPrime_polynomial (FractionRing D) _
  exact kmf2_polyasc_isRegularLocalRing_atPrime_of_isLocalization_primeCompl Q
    (Localization.AtPrime
      (Q.map (algebraMap (Polynomial D) (Polynomial (FractionRing D)))))
    hQloc hregq

theorem kmf2_polyasc_isRegularLocalRing_localization_atPrime_fiberPrime
    (R : Type u) [CommRing R] (P : Ideal (Polynomial R)) [P.IsPrime]
    [hPbar : (P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.under R)))).IsPrime] :
    IsRegularLocalRing (Localization.AtPrime
      (P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.under R))))) := by
  have hIP : Ideal.map Polynomial.C (P.under R) ≤ P := by
    rw [Ideal.map_le_iff_le_comap, ← Polynomial.algebraMap_eq]
  have : IsRegularLocalRing (Localization.AtPrime
      ((P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.under R)))).comap
        (P.under R).polynomialQuotientEquivQuotientPolynomial)) := by
    apply kmf2_polyasc_isRegularLocalRing_localization_atPrime_of_comap_C_eq_bot
      (R ⧸ P.under R)
    intro d hd
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [Ideal.mem_comap,
      show (Polynomial.C ((Ideal.Quotient.mk (P.under R)) r)) =
        (Polynomial.C r).map (Ideal.Quotient.mk (P.under R)) from (Polynomial.map_C _).symm,
      Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk] at hd
    obtain ⟨a, haP, hab⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hd
    have hsub : a - Polynomial.C r ∈ Ideal.map Polynomial.C (P.under R) :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hab
    have hCrP : Polynomial.C r ∈ P := by
      have h2 := P.sub_mem haP (hIP hsub)
      rwa [sub_sub_cancel] at h2
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change r ∈ P.under R
    rw [Ideal.mem_comap]
    rwa [Polynomial.algebraMap_eq]
  exact IsRegularLocalRing.of_ringEquiv
    (R := Localization.AtPrime
      ((P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.under R)))).comap
        (P.under R).polynomialQuotientEquivQuotientPolynomial))
    (IsLocalization.ringEquivOfRingEquiv
      (Localization.AtPrime
        ((P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.under R)))).comap
          (P.under R).polynomialQuotientEquivQuotientPolynomial))
      (Localization.AtPrime
        (P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.under R)))))
      (P.under R).polynomialQuotientEquivQuotientPolynomial
      (((P.under R).polynomialQuotientEquivQuotientPolynomial).map_primeCompl_comap_eq
        (P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.under R))))))

theorem kmf2_polyasc_isRegularLocalRing_quotient_fiber
    (R : Type u) [CommRing R] (P : Ideal (Polynomial R)) [P.IsPrime] :
    IsRegularLocalRing
      (Localization.AtPrime P ⧸
        Ideal.map (algebraMap (Polynomial R) (Localization.AtPrime P))
          (Ideal.map Polynomial.C (P.under R))) := by
  have hIP : Ideal.map Polynomial.C (P.under R) ≤ P := by
    rw [Ideal.map_le_iff_le_comap, ← Polynomial.algebraMap_eq]
  have hPbar : (P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.under R)))).IsPrime := by
    refine Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective ?_
    rw [Ideal.mk_ker]
    exact hIP
  have hsub : Algebra.algebraMapSubmonoid
      (Polynomial R ⧸ Ideal.map Polynomial.C (P.under R)) P.primeCompl
      = (P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.under R)))).primeCompl := by
    ext x
    constructor
    · intro hx
      obtain ⟨b, hb, rfl⟩ := Submonoid.mem_map.mp hx
      rw [Ideal.mem_primeCompl_iff]
      rw [Ideal.Quotient.algebraMap_eq]
      intro hmem
      obtain ⟨a, haP, hab⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hmem
      have hd : a - b ∈ Ideal.map Polynomial.C (P.under R) :=
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hab
      have hbP : b ∈ P := by
        have h2 := P.sub_mem haP (hIP hd)
        rwa [sub_sub_cancel] at h2
      exact (Ideal.mem_primeCompl_iff.mp hb) hbP
    · intro hx
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine Submonoid.mem_map.mpr ⟨b, ?_, by rw [Ideal.Quotient.algebraMap_eq]⟩
      rw [Ideal.mem_primeCompl_iff]
      intro hbP
      exact (Ideal.mem_primeCompl_iff.mp hx) (Ideal.mem_map_of_mem _ hbP)
  have hloc2 : IsLocalization
      (P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.under R)))).primeCompl
      (Localization.AtPrime P ⧸
        Ideal.map (algebraMap (Polynomial R) (Localization.AtPrime P))
          (Ideal.map Polynomial.C (P.under R))) := by
    have h0 : IsLocalization
        (Algebra.algebraMapSubmonoid
          (Polynomial R ⧸ Ideal.map Polynomial.C (P.under R)) P.primeCompl)
        (Localization.AtPrime P ⧸
          Ideal.map (algebraMap (Polynomial R) (Localization.AtPrime P))
            (Ideal.map Polynomial.C (P.under R))) := inferInstance
    rwa [hsub] at h0
  have hPbarReg : IsRegularLocalRing (Localization.AtPrime
      (P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.under R))))) :=
    kmf2_polyasc_isRegularLocalRing_localization_atPrime_fiberPrime R P
  exact kmf2_polyasc_isRegularLocalRing_of_isLocalization_primeCompl
    (P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.under R))))
    (Localization.AtPrime P ⧸
      Ideal.map (algebraMap (Polynomial R) (Localization.AtPrime P))
        (Ideal.map Polynomial.C (P.under R)))
    hloc2 hPbarReg

theorem kmf2_polyasc_isRegularLocalRing_localization_atPrime_polynomial_of_isRegularRing
    (R : Type u) [CommRing R] [IsRegularRing R]
    (P : Ideal (Polynomial R)) [P.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime P) := by
  exact IsRegularRing.isRegularLocalRing_localization P

theorem kmf2_polyasc_isRegularRing_polynomial_of_isRegularRing
    (R : Type u) [CommRing R] [IsRegularRing R] :
    IsRegularRing (Polynomial R) := by
  infer_instance

theorem kmf2_polyasc_isRegularRing_mvPolynomial_fin
    (k : Type u) [Field k] (n : ℕ) :
    IsRegularRing (MvPolynomial (Fin n) k) := by
  infer_instance

theorem kmf2_polyasc_gate_input_clause_mvPolynomial
    (k : Type u) [Field k] (n : ℕ) :
    Algebra.Smooth k (MvPolynomial (Fin n) k) ∧
      ∀ (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime],
        IsRegularLocalRing (Localization.AtPrime P) := by
  refine ⟨inferInstance, ?_⟩
  intro P hP
  have : IsRegularRing (MvPolynomial (Fin n) k) :=
    kmf2_polyasc_isRegularRing_mvPolynomial_fin k n
  exact IsRegularRing.isRegularLocalRing_localization P

theorem kmf2_polyasc_gate_isRegularRing_polynomial_int :
    IsRegularRing (Polynomial ℤ) := by
  have : IsRegularRing ℤ := by
    have : IsDedekindDomain ℤ := inferInstance
    infer_instance
  exact kmf2_polyasc_isRegularRing_polynomial_of_isRegularRing ℤ

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.FrobeniusLocalization


universe u

namespace FrobeniusIndependence

/-- Frobenius independence for finite coefficient families. -/
def PR (k : Type u) [Field k] (p : ℕ) (C : Type u) [CommRing C] [Algebra k C] : Prop :=
  ∀ (n : ℕ) (a : Fin n → k) (y : Fin n → C),
    (∀ d : Fin n → k, ∑ j, d j ^ p * a j = 0 → d = 0) → ∑ j, a j • y j ^ p = 0 → y = 0

variable {k : Type u} [Field k] {p : ℕ}

theorem PR.of_injective {C D : Type u} [CommRing C] [Algebra k C] [CommRing D] [Algebra k D]
    (f : C →ₐ[k] D) (hf : Function.Injective f) (h : PR k p D) : PR k p C := by
  intro n a y hind hsum
  have : (fun j => f (y j)) = 0 := by
    apply h n a _ hind
    have := congrArg f hsum
    rw [map_sum, map_zero] at this
    simpa only [map_smul, map_pow] using this
  funext j
  apply hf
  have hj := congrFun this j
  simp only [Pi.zero_apply] at hj
  rw [hj, Pi.zero_apply, map_zero]

theorem PR.of_dense {B : Type u} [CommRing B] [Algebra k B] (S : Set (PrimeSpectrum B))
    (hdense : ∀ g : B, (∀ 𝔰 ∈ S, g ∈ 𝔰.asIdeal) → g = 0)
    (hS : ∀ 𝔰 ∈ S, PR k p 𝔰.asIdeal.ResidueField) : PR k p B := by
  intro n a y hind hsum
  funext j
  apply hdense
  intro 𝔰 h𝔰
  have h := hS 𝔰 h𝔰 n a (fun j => algebraMap B 𝔰.asIdeal.ResidueField (y j)) hind (by
    have := congrArg (IsScalarTower.toAlgHom k B 𝔰.asIdeal.ResidueField) hsum
    rw [map_sum, map_zero] at this
    simpa only [map_smul, map_pow, IsScalarTower.coe_toAlgHom'] using this)
  have hj := congrFun h j
  simp only [Pi.zero_apply] at hj
  exact Ideal.algebraMap_residueField_eq_zero.mp hj

theorem PR.localization {B : Type u} [CommRing B] [Algebra k B] (hp : 0 < p) (M : Submonoid B)
    (L : Type u) [CommRing L] [Algebra B L] [Algebra k L] [IsScalarTower k B L] [IsLocalization M L]
    (h : PR k p B) : PR k p L := by
  intro n a y hind hsum
  classical
  obtain ⟨u, hu⟩ := IsLocalization.exist_integer_multiples_of_finite M y
  choose b hb using hu
  have h1 : algebraMap B L (∑ j, a j • b j ^ p) = 0 := by
    have e1 : (IsScalarTower.toAlgHom k B L) (∑ j, a j • b j ^ p) =
        ∑ j, algebraMap B L u ^ p * (a j • y j ^ p) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, map_pow, IsScalarTower.coe_toAlgHom', hb j, Algebra.smul_def (↑u : B), mul_pow,
          ← mul_smul_comm]
    rw [IsScalarTower.coe_toAlgHom'] at e1
    rw [e1, ← Finset.mul_sum, hsum, mul_zero]
  obtain ⟨v, hv⟩ := (IsLocalization.map_eq_zero_iff M L _).mp h1
  have h2 : ∑ j, a j • ((v : B) * b j) ^ p = 0 := by
    have e2 : ∀ j, a j • ((v : B) * b j) ^ p = (v : B) ^ p * (a j • b j ^ p) := by
      intro j; rw [mul_pow, ← mul_smul_comm]
    simp only [e2]
    rw [← Finset.mul_sum]
    calc (v : B) ^ p * ∑ j, a j • b j ^ p = (v : B) ^ (p - 1) * ((v : B) * ∑ j, a j • b j ^ p) := by
          rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp]
      _ = 0 := by rw [hv, mul_zero]
  have h3 := h n a (fun j => (v : B) * b j) hind h2
  funext j
  have hj : (v : B) * b j = 0 := congrFun h3 j
  have : algebraMap B L v * algebraMap B L (b j) = 0 := by rw [← map_mul, hj, map_zero]
  rw [hb j, Algebra.smul_def (↑u : B), (IsLocalization.map_units L v).mul_right_eq_zero,
    (IsLocalization.map_units L u).mul_right_eq_zero] at this
  exact this

theorem PR.of_field (K : Type u) [Field K] [Algebra k K] (hp : p.Prime) [CharP K p]
    (HK : ∀ t : Finset K, LinearIndepOn k _root_.id (t : Set K) → LinearIndepOn k (· ^ p) (t : Set
        K)) :
    PR k p K := by
  intro n a y hind hsum
  classical
  have : Fact p.Prime := ⟨hp⟩
  let V : Submodule k K := Submodule.span k (Set.range y)
  have : Module.Finite k V := Module.Finite.span_of_finite k (Set.finite_range y)
  let bV := Module.finBasis k V
  let w : Fin (Module.finrank k V) → K := fun i => (bV i : K)
  have hw : LinearIndependent k w := bV.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hwinj : Function.Injective w := hw.injective
  have hwp : LinearIndependent k (fun i => w i ^ p) := by
    have h1 : LinearIndepOn k _root_.id ((Finset.univ.image w : Finset K) : Set K) := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact hw.linearIndepOn_id
    have h2 := HK _ h1
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, linearIndepOn_range_iff hwinj] at h2
    exact h2
  have hyV : ∀ j, y j ∈ V := fun j => Submodule.subset_span ⟨j, rfl⟩
  let μ : Fin n → Fin (Module.finrank k V) → k := fun j i => bV.repr ⟨y j, hyV j⟩ i
  have hy : ∀ j, y j = ∑ i, μ j i • w i := by
    intro j
    have := bV.sum_repr ⟨y j, hyV j⟩
    have := congrArg (fun v : V => (v : K)) this
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hyp : ∀ j, y j ^ p = ∑ i, μ j i ^ p • w i ^ p := by
    intro j
    rw [hy j, sum_pow_char]
    simp only [smul_pow]
  have hsum' : ∑ i, (∑ j, a j * μ j i ^ p) • w i ^ p = 0 := by
    rw [← hsum]
    simp only [hyp, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  have hcoef : ∀ i, ∑ j, a j * μ j i ^ p = 0 := Fintype.linearIndependent_iff.mp hwp _ hsum'
  have hμ : ∀ j i, μ j i = 0 := by
    intro j i
    have := hind (fun j => μ j i) (by simpa only [mul_comm] using hcoef i)
    exact congrFun this j
  funext j
  rw [Pi.zero_apply, hy j]
  simp only [hμ, zero_smul, Finset.sum_const_zero]

theorem linearIndepOn_pow_of_PR (L : Type u) [Field L] [Algebra k L] (hp : p.Prime) [ExpChar k p]
    [CharP L p]
    (h : PR k p L) (t : Finset L) (ht : LinearIndepOn k _root_.id (t : Set L)) :
    LinearIndepOn k (· ^ p) (t : Set L) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  unfold LinearIndepOn at ht ⊢
  rw [Fintype.linearIndependent_iff] at ht ⊢
  intro g hg
  let K₀ : Subfield k := (frobenius k p).fieldRange
  let W : Submodule K₀ k := Submodule.span K₀ (Set.range g)
  have : Module.Finite K₀ W := Module.Finite.span_of_finite K₀ (Set.finite_range g)
  let bW := Module.finBasis K₀ W
  let aW : Fin (Module.finrank K₀ W) → k := fun m => (bW m : k)
  have hind : ∀ d : Fin (Module.finrank K₀ W) → k, ∑ m, d m ^ p * aW m = 0 → d = 0 := by
    intro d hd
    have hd' : ∑ m, (⟨d m ^ p, RingHom.mem_fieldRange_self (f := frobenius k p) (d m)⟩ : K₀) • bW m
        = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero]
      simp only [Submodule.coe_smul] at hd ⊢
      exact hd
    have := Fintype.linearIndependent_iff.mp bW.linearIndependent _ hd'
    funext m
    have hm := congrArg Subtype.val (this m)
    exact pow_eq_zero_iff hp.ne_zero |>.mp hm
  have hgW : ∀ x, g x ∈ W := fun x => Submodule.subset_span ⟨x, rfl⟩
  let κ : ↥(t : Set L) → Fin (Module.finrank K₀ W) → K₀ := fun x m => bW.repr ⟨g x, hgW x⟩ m
  have hgexp : ∀ x, g x = ∑ m, (κ x m : k) * aW m := by
    intro x
    have := bW.sum_repr ⟨g x, hgW x⟩
    have := congrArg (fun v : W => (v : k)) this
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hκ : ∀ x m, ∃ e : k, e ^ p = (κ x m : k) := by
    intro x m
    obtain ⟨e, he⟩ := RingHom.mem_fieldRange.mp (κ x m).2
    exact ⟨e, by rw [← he, frobenius_def]⟩
  choose e he using hκ
  have hY : ∑ m, aW m • (∑ x, e x m • (x : L)) ^ p = 0 := by
    rw [← hg]
    simp only [sum_pow_char, smul_pow, Finset.smul_sum, smul_smul, hgexp, Finset.sum_smul, he]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comm]
  have hzero := h _ aW (fun m => ∑ x, e x m • (x : L)) hind hY
  have he0 : ∀ x m, e x m = 0 := by
    intro x m
    have hm : ∑ x, e x m • (x : L) = 0 := congrFun hzero m
    exact ht (fun x => e x m) hm x
  intro x
  rw [hgexp x]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [← he x m, he0 x m, zero_pow hp.ne_zero, zero_mul]

end FrobeniusIndependence

open FrobeniusIndependence

theorem _root_.Algebra.linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense
    {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
        [IsReduced B]
    (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (S : Set (PrimeSpectrum B))
    (hdense : ∀ g : B, (∀ 𝔰 ∈ S, g ∈ 𝔰.asIdeal) → g = 0)
    (hsep : ∀ 𝔰 ∈ S, ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      (∀ t : Finset K, LinearIndepOn k _root_.id (t : Set K) → LinearIndepOn k (· ^ p) (t : Set K))
          ∧
      Nonempty (𝔰.asIdeal.ResidueField →ₐ[k] K))
    (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔮 : 𝔮 ∈ minimalPrimes B)
    (s : Finset (Localization.AtPrime 𝔮)) (hs : LinearIndepOn k _root_.id (s : Set
        (Localization.AtPrime 𝔮))) :
    LinearIndepOn k (· ^ p) (s : Set (Localization.AtPrime 𝔮)) := by
  classical
  have : CharP k p := by
    obtain h0 | ⟨p', hp', hc⟩ := CharP.exists' k
    · have h1 : 1 = p := ExpChar.eq (@ExpChar.zero k _ h0) ‹ExpChar k p›
      exact absurd h1 hp.one_lt.ne
    · have h1 : p' = p := ExpChar.eq (@ExpChar.prime k _ p' hp'.out hc) ‹ExpChar k p›
      exact h1 ▸ hc
  have hRS : ∀ 𝔰 ∈ S, PR k p 𝔰.asIdeal.ResidueField := by
    intro 𝔰 h𝔰
    obtain ⟨K, iF, iA, hK, ⟨φ⟩⟩ := hsep 𝔰 h𝔰
    have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
    exact PR.of_injective φ φ.toRingHom.injective (PR.of_field K hp hK)
  have hRB : PR k p B := PR.of_dense S hdense hRS
  have hRL : PR k p (Localization.AtPrime 𝔮) := PR.localization hp.pos 𝔮.primeCompl _ hRB
  have hrad : ((⊥ : Ideal B).map (algebraMap B (Localization.AtPrime 𝔮))).radical =
      𝔮.map (algebraMap B (Localization.AtPrime 𝔮)) :=
    IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := Localization.AtPrime 𝔮) 𝔮 ⊥ h𝔮
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮) = ⊥ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← hrad, Ideal.map_bot]
    exact nilradical_eq_zero (Localization.AtPrime 𝔮)
  have hfield : IsField (Localization.AtPrime 𝔮) := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmax
  let : Field (Localization.AtPrime 𝔮) := hfield.toField
  have : CharP (Localization.AtPrime 𝔮) p :=
    charP_of_injective_algebraMap (algebraMap k (Localization.AtPrime 𝔮)).injective p
  exact linearIndepOn_pow_of_PR (Localization.AtPrime 𝔮) hp hRL s hs

end AbelianVarieties.NOSProofs.FrobeniusLocalization
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_FormallySmooth_linearIndepOn_pow_of_linearIndepOn_id.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.SmoothFrobenius


universe u
open TensorProduct
theorem Algebra.FormallySmooth.linearIndepOn_pow_aux29
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.FormallySmooth k K]
    (p : ℕ) (hp : p.Prime) [ExpChar k p] :
    ∀ s : Finset K, LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (· ^ p) (s : Set K) :=
        by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hchark : CharP k p := by
    cases ‹ExpChar k p› with
    | zero => exact absurd hp Nat.not_prime_one
    | prime hprime => assumption
  have hcharK : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  let k₀ : Subfield k := ⊥
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange k₀ k K) := by
    have hex := Algebra.H1Cotangent.exact_δ_mapBaseChange k₀ k K
    have : Subsingleton (Algebra.H1Cotangent k K) := Algebra.FormallySmooth.subsingleton_h1Cotangent
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨y, rfl⟩ := (hex x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  let B := Module.Free.chooseBasis k (Ω[k⁄k₀])
  let BK := B.baseChange K
  intro s
  induction s using Finset.strongInduction with
  | H s IH =>
    intro hs
    rw [linearIndepOn_finset_iff]
    intro g hg
    by_contra hne
    push Not at hne
    obtain ⟨x₀, hx₀, hgx₀⟩ := hne
    set c : K → k := fun x => (g x₀)⁻¹ * g x with hc
    have hc₀ : c x₀ = 1 := inv_mul_cancel₀ hgx₀
    have hrel : ∑ x ∈ s, c x • x ^ p = 0 := by
      simp only [hc, mul_smul, ← Finset.smul_sum, hg, smul_zero]
    have hD : ∀ x ∈ s, KaehlerDifferential.D k₀ k (c x) = 0 := by
      set T : K ⊗[k] Ω[k⁄k₀] := ∑ x ∈ s, (x ^ p) ⊗ₜ[k] KaehlerDifferential.D k₀ k (c x) with hT
      have hT0 : T = 0 := by
        apply hinj
        rw [map_zero, hT, map_sum]
        simp_rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
        have hDrel := congrArg (KaehlerDifferential.D k₀ K) hrel
        rw [map_zero, map_sum] at hDrel
        rw [← hDrel]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Algebra.smul_def, Derivation.leibniz, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul
            K, CharP.cast_eq_zero,
          zero_smul, smul_zero, zero_add]
      have hcoord : ∀ j, ∑ x ∈ s, (B.repr (KaehlerDifferential.D k₀ k (c x)) j) • x ^ p = 0 := by
        intro j
        have := congrArg (fun t => BK.repr t j) hT0
        simp only [hT, map_sum, map_zero, Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_finsetSum,
            Finset.sum_apply,
          Module.Basis.baseChange_repr_tmul, BK] at this
        exact this
      have hsub : s.erase x₀ ⊂ s := Finset.erase_ssubset hx₀
      have hind' : LinearIndepOn k (· ^ p) ((s.erase x₀ : Finset K) : Set K) :=
        IH _ hsub (hs.mono (by intro y hy; exact Finset.mem_of_mem_erase (Finset.mem_coe.mp hy)))
      rw [linearIndepOn_finset_iff] at hind'
      have hzero : ∀ j, ∀ x ∈ s, B.repr (KaehlerDifferential.D k₀ k (c x)) j = 0 := by
        intro j x hx
        by_cases hxx : x = x₀
        · subst hxx; rw [hc₀, Derivation.map_one_eq_zero, map_zero, Finsupp.zero_apply]
        · apply hind' (fun x => B.repr (KaehlerDifferential.D k₀ k (c x)) j) _ x
            (Finset.mem_erase.mpr ⟨hxx, hx⟩)
          have h0 : B.repr (KaehlerDifferential.D k₀ k (c x₀)) j • x₀ ^ p = 0 := by
            rw [hc₀, Derivation.map_one_eq_zero, map_zero, Finsupp.zero_apply, zero_smul]
          have := Finset.add_sum_erase s (fun x => B.repr (KaehlerDifferential.D k₀ k (c x)) j • x
              ^ p) hx₀
          rw [hcoord j, h0, zero_add] at this
          exact this
      intro x hx
      apply B.repr.injective
      rw [map_zero]
      ext j
      rw [hzero j x hx, Finsupp.zero_apply]
    have hroot : ∀ x ∈ s, ∃ b : k, b ^ p = c x := by
      intro x hx
      by_contra h
      push Not at h
      exact KaehlerDifferential.D_ne_zero_of_forall_pow_ne p hp (c x) h (hD x hx)
    choose! b hb using hroot
    have hsum : (∑ x ∈ s, b x • x) ^ p = 0 := by
      rw [sum_pow_char p, ← hrel]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Algebra.smul_def, Algebra.smul_def, mul_pow, ← map_pow, hb x hx]
    have hsum0 : ∑ x ∈ s, b x • x = 0 := pow_eq_zero_iff hp.ne_zero |>.mp hsum
    rw [linearIndepOn_finset_iff] at hs
    have hb0 := hs b hsum0 x₀ hx₀
    have : c x₀ = 0 := by rw [← hb x₀ hx₀, hb0, zero_pow hp.ne_zero]
    rw [hc₀] at this
    exact one_ne_zero this

theorem _root_.Algebra.FormallySmooth.linearIndepOn_pow_of_linearIndepOn_id
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.FormallySmooth k K]
    (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (s : Finset K) (hs : LinearIndepOn k _root_.id (s : Set K)) :
    LinearIndepOn k (· ^ p) (s : Set K) := by
  exact Algebra.FormallySmooth.linearIndepOn_pow_aux29 p hp s hs

end AbelianVarieties.NOSProofs.SmoothFrobenius
end
