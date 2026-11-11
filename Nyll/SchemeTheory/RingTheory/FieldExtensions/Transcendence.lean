/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Util.WithWeakNamespace
public import Nyll.SchemeTheory.RingTheory.AlgebraNeZeroAlgebraicIndependentIsIntegralPowSmul

/-!
# Transcendence degree of tensor products and Krull dimension
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_TensorProduct_trdeg_quotient_le_and_mem_minimalPrimes_iff_of_mem_minimalPrimes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace TensorTranscendence
open TensorProduct Polynomial

universe u

namespace TensorPrimes

section General

theorem isAlgebraic_of_smul' {R A : Type*} [CommRing R] [IsDomain R] [Ring A] [Algebra R A] {z : A}
    {y : R}
    (hy : y ≠ 0) (h : IsAlgebraic R (y • z)) : IsAlgebraic R z :=
  IsAlgebraic.of_smul (mem_nonZeroDivisors_of_ne_zero hy) h

theorem isIntegral_map_of_forall_mem {R R' C C' : Type*} [CommRing R] [CommRing R'] [CommRing C]
    [CommRing C']
    [Algebra R C] [Algebra R' C'] (f : C →+* C') (D : Subalgebra R C) (D' : Subalgebra R' C')
    (hDD' : ∀ x ∈ D, f x ∈ D') {x : C} (hx : IsIntegral D x) : IsIntegral D' (f x) := by
  obtain ⟨p, hmonic, hp⟩ := hx
  let φ : D →+* D' := (f.comp (algebraMap D C)).codRestrict D'.toSubring
    (fun d => hDD' _ (by exact d.2))
  have hφ : (algebraMap D' C').comp φ = f.comp (algebraMap D C) := by
    ext d; rfl
  refine ⟨p.map φ, hmonic.map φ, ?_⟩
  rw [eval₂_map, hφ, ← hom_eval₂, hp, map_zero]

theorem isAlgebraic_quotient_of_noether {E₀ E₀' C C' : Type*} [CommRing E₀] [CommRing E₀']
    [IsDomain E₀']
    [CommRing C] [CommRing C'] [IsDomain C']
    [Algebra E₀ C] [Algebra E₀' C'] [FaithfulSMul E₀' C'] (πR : E₀ →+* E₀') (πC : C →+* C')
    (hπ : ∀ x : E₀, πC (algebraMap E₀ C x) = algebraMap E₀' C' (πR x)) (hπsurj :
        Function.Surjective πC)
    {d : ℕ} (z : Fin d → C) (r : E₀) (hr : πR r ≠ 0)
    (hint : ∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin E₀ (Set.range z)) (r ^ n • c)) :
    ∀ x ∈ (⊤ : Subalgebra E₀' C'), IsAlgebraic (Algebra.adjoin E₀' (Set.range (fun i => πC (z i))))
        x := by
  intro c' _
  set D : Subalgebra E₀ C := Algebra.adjoin E₀ (Set.range z)
  set D' : Subalgebra E₀' C' := Algebra.adjoin E₀' (Set.range (fun i => πC (z i)))
  have hDD' : ∀ x ∈ D, πC x ∈ D' := by
    intro x hx
    refine Algebra.adjoin_induction (hx := hx) ?_ ?_ ?_ ?_
    · rintro _ ⟨i, rfl⟩; exact Algebra.subset_adjoin ⟨i, rfl⟩
    · intro x; rw [hπ]; exact Subalgebra.algebraMap_mem _ _
    · intro x y _ _ hx hy; rw [map_add]; exact D'.add_mem hx hy
    · intro x y _ _ hx hy; rw [map_mul]; exact D'.mul_mem hx hy
  obtain ⟨c, rfl⟩ := hπsurj c'
  obtain ⟨n, hn⟩ := hint c
  have h1 : IsIntegral D' (πC (r ^ n • c)) := isIntegral_map_of_forall_mem πC D D' hDD' hn
  simp only [Algebra.smul_def, map_pow, map_mul] at h1
  rw [hπ] at h1
  let ρ : D' := ⟨algebraMap E₀' C' (πR r) ^ n, D'.pow_mem (Subalgebra.algebraMap_mem _ _) n⟩
  have hρ : (ρ : C') ≠ 0 := by
    refine pow_ne_zero _ ?_
    rw [Ne, ← map_zero (algebraMap E₀' C'), (FaithfulSMul.algebraMap_injective E₀' C').eq_iff]
    exact hr
  have hρ' : ρ ≠ 0 := fun h => hρ (by rw [h]; rfl)
  have h2 : IsAlgebraic D' (ρ • πC c) := by
    rw [Algebra.smul_def]
    exact h1.isAlgebraic
  exact isAlgebraic_of_smul' hρ' h2

theorem exists_monic_aeval_eq_zero_coeff_ne_zero {D C : Type*} [CommRing D] [CommRing C] [IsDomain
    C] [Algebra D C]
    {y : C} (hy : y ≠ 0) (hint : IsIntegral D y) :
    ∃ p : D[X], p.Monic ∧ aeval y p = 0 ∧ p.coeff 0 ≠ 0 := by
  classical
  have hex : ∃ n : ℕ, ∃ p : D[X], p.Monic ∧ aeval y p = 0 ∧ p.natDegree = n := by
    obtain ⟨p, hp, hpy⟩ := hint
    exact ⟨p.natDegree, p, hp, by rwa [aeval_def], rfl⟩
  obtain ⟨p, hp, hpy, hpn⟩ := Nat.find_spec hex
  have hmin : ∀ q : D[X], q.Monic → aeval y q = 0 → p.natDegree ≤ q.natDegree := by
    intro q hq hqy
    rw [hpn]
    exact Nat.find_min' hex ⟨q, hq, hqy, rfl⟩
  refine ⟨p, hp, hpy, fun h0 => ?_⟩
  have hp' : X * p.divX = p := by
    have := X_mul_divX_add p
    rw [h0, map_zero, add_zero] at this
    exact this
  have hnd : p.natDegree ≠ 0 := by
    intro h
    have h1 : p = 1 := hp.natDegree_eq_zero.mp h
    rw [h1, map_one] at hpy
    exact one_ne_zero hpy
  have hdiv_monic : p.divX.Monic := by
    have h := hp
    rw [← hp'] at h
    exact Monic.of_mul_monic_left monic_X h
  have hdiv_deg : p.divX.natDegree < p.natDegree := by
    rw [natDegree_divX_eq_natDegree_tsub_one]
    omega
  have hdiv_y : aeval y p.divX = 0 := by
    have h := hpy
    rw [← hp', map_mul, aeval_X] at h
    exact (mul_eq_zero.mp h).resolve_left hy
  exact absurd (hmin _ hdiv_monic hdiv_y) (not_le.mpr hdiv_deg)

end General

section StrictDrop

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

theorem trdeg_quotient_lt_of_lt [Algebra.FiniteType A B] (𝔭 : Ideal A) [𝔭.IsPrime] (Q 𝔓 : Ideal B)
    [Q.IsPrime]
    [𝔓.IsPrime] [Q.LiesOver 𝔭] [𝔓.LiesOver 𝔭] (hlt : Q < 𝔓) :
    Algebra.trdeg (A ⧸ 𝔭) (B ⧸ 𝔓) < Algebra.trdeg (A ⧸ 𝔭) (B ⧸ Q) := by
  classical
  have : Algebra.FiniteType (A ⧸ 𝔭) (B ⧸ Q) := by
    have h : 𝔭 = Q.under A := Q.over_def 𝔭
    subst h
    infer_instance
  obtain ⟨r, hr, e, z, hz, hint⟩ :=
    Algebra.exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType
      (R := A ⧸ 𝔭) (C := B ⧸ Q)
  have halgC : Algebra.IsAlgebraic (Algebra.adjoin (A ⧸ 𝔭) (Set.range z)) (B ⧸ Q) := by
    have h := isAlgebraic_quotient_of_noether (E₀ := A ⧸ 𝔭) (E₀' := A ⧸ 𝔭) (C := B ⧸ Q) (C' := B ⧸
        Q)
      (RingHom.id _) (RingHom.id _) (fun _ => rfl) Function.surjective_id z r hr hint
    exact ⟨fun x => h x trivial⟩
  have hbasis : IsTranscendenceBasis (A ⧸ 𝔭) z := hz.isTranscendenceBasis_iff_isAlgebraic.mpr halgC
  have he : (e : Cardinal.{u}) = Algebra.trdeg (A ⧸ 𝔭) (B ⧸ Q) := by
    have h := hbasis.lift_cardinalMk_eq_trdeg
    simpa only [Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_uzero] using h
  rw [← he]
  let π : B ⧸ Q →+* B ⧸ 𝔓 := Ideal.Quotient.factor hlt.le
  have hπ : ∀ x : A ⧸ 𝔭, π (algebraMap (A ⧸ 𝔭) (B ⧸ Q) x) = algebraMap (A ⧸ 𝔭) (B ⧸ 𝔓) x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  have hπsurj : Function.Surjective π := Ideal.Quotient.factor_surjective hlt.le
  let z' : Fin e → B ⧸ 𝔓 := fun i => π (z i)
  have halg : Algebra.IsAlgebraic (Algebra.adjoin (A ⧸ 𝔭) (Set.range z')) (B ⧸ 𝔓) := by
    have h := isAlgebraic_quotient_of_noether (E₀ := A ⧸ 𝔭) (E₀' := A ⧸ 𝔭) (C := B ⧸ Q) (C' := B ⧸
        𝔓)
      (RingHom.id _) π hπ hπsurj z r hr hint
    exact ⟨fun x => h x trivial⟩
  obtain ⟨t, ht, htb⟩ := (isAlgebraic_iff_exists_isTranscendenceBasis_subset (R := A ⧸ 𝔭) (A := B ⧸
      𝔓)
    (s := Set.range z')).mp halg
  have htcard : Cardinal.mk t = Algebra.trdeg (A ⧸ 𝔭) (B ⧸ 𝔓) := htb.cardinalMk_eq_trdeg
  have hdep : ¬ AlgebraicIndependent (A ⧸ 𝔭) z' := by
    intro hind
    obtain ⟨b, hb𝔓, hbQ⟩ := Set.exists_of_ssubset hlt
    have hc0 : Ideal.Quotient.mk Q b ≠ 0 := fun h => hbQ (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hcπ : π (Ideal.Quotient.mk Q b) = 0 := by
      change Ideal.Quotient.mk 𝔓 b = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hb𝔓
    obtain ⟨n, hn⟩ := hint (Ideal.Quotient.mk Q b)
    have hy0 : r ^ n • Ideal.Quotient.mk Q b ≠ 0 := by
      rw [Algebra.smul_def, map_pow]
      refine mul_ne_zero (pow_ne_zero _ ?_) hc0
      rw [Ne, ← map_zero (algebraMap (A ⧸ 𝔭) (B ⧸ Q)), (FaithfulSMul.algebraMap_injective (A ⧸ 𝔭)
          (B ⧸ Q)).eq_iff]
      exact hr
    have hyπ : π (r ^ n • Ideal.Quotient.mk Q b) = 0 := by
      rw [Algebra.smul_def, map_mul, hcπ, mul_zero]
    obtain ⟨p, hpm, hpy, hp0⟩ := exists_monic_aeval_eq_zero_coeff_ne_zero hy0 hn
    have hker : π (algebraMap _ (B ⧸ Q) (p.coeff 0)) = 0 := by
      have h := X_mul_divX_add p
      have h2 : aeval (r ^ n • Ideal.Quotient.mk Q b) (X * p.divX + C (p.coeff 0)) = 0 := by
        rw [h]
        exact hpy
      rw [map_add, map_mul, aeval_X, aeval_C] at h2
      have h3 := eq_neg_of_add_eq_zero_right h2
      rw [h3, map_neg, map_mul, hyπ, zero_mul, neg_zero]
    have hcomp : (π.comp (algebraMap (Algebra.adjoin (A ⧸ 𝔭) (Set.range z)) (B ⧸ Q))).comp
        (hz.aevalEquiv : MvPolynomial (Fin e) (A ⧸ 𝔭) →+* Algebra.adjoin (A ⧸ 𝔭) (Set.range z)) =
        (MvPolynomial.aeval (R := A ⧸ 𝔭) z').toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro x
        change π (algebraMap _ (B ⧸ Q) (hz.aevalEquiv (MvPolynomial.C x))) = MvPolynomial.aeval z'
            (MvPolynomial.C x)
        rw [hz.algebraMap_aevalEquiv, MvPolynomial.aeval_C, MvPolynomial.aeval_C]
        exact hπ x
      · intro i
        change π (algebraMap _ (B ⧸ Q) (hz.aevalEquiv (MvPolynomial.X i))) = MvPolynomial.aeval z'
            (MvPolynomial.X i)
        rw [hz.algebraMap_aevalEquiv, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    have hinj : Function.Injective (π.comp (algebraMap (Algebra.adjoin (A ⧸ 𝔭) (Set.range z)) (B ⧸
        Q))) := by
      have h1 : Function.Injective ((π.comp (algebraMap (Algebra.adjoin (A ⧸ 𝔭) (Set.range z)) (B ⧸
          Q))).comp
          (hz.aevalEquiv : MvPolynomial (Fin e) (A ⧸ 𝔭) →+* Algebra.adjoin (A ⧸ 𝔭) (Set.range z)))
              := by
        rw [hcomp]
        exact algebraicIndependent_iff_injective_aeval.mp hind
      exact Function.Injective.of_comp_right (f := π.comp (algebraMap _ (B ⧸ Q))) h1
          hz.aevalEquiv.surjective
    have h0 : p.coeff 0 = 0 := by
      apply hinj
      rw [RingHom.comp_apply, hker, map_zero]
    exact hp0 h0
  have hfin : (Set.range z').Finite := Set.finite_range z'
  have htfin : t.Finite := hfin.subset ht
  have h1 : Cardinal.mk t ≤ Cardinal.mk (Set.range z') := Cardinal.mk_le_mk_of_subset ht
  have h2 : Cardinal.mk (Set.range z') ≤ (e : Cardinal.{u}) := by
    simpa only [Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_uzero] using
      Cardinal.mk_range_le_lift (f := z')
  rw [← htcard]
  refine lt_of_le_of_ne (h1.trans h2) fun heq => hdep ?_
  have hrange : Cardinal.mk (Set.range z') = (e : Cardinal.{u}) := le_antisymm h2 (heq ▸ h1)
  have hncard_t : (t.ncard : Cardinal.{u}) = e := by rw [Set.cast_ncard htfin]; exact heq
  have hncard_r : ((Set.range z').ncard : Cardinal.{u}) = e := by
    rw [Set.cast_ncard hfin]
    exact hrange
  have hnt : t.ncard = e := by exact_mod_cast hncard_t
  have hnr : (Set.range z').ncard = e := by exact_mod_cast hncard_r
  have hteq : t = Set.range z' := Set.eq_of_subset_of_ncard_le ht (by rw [hnt, hnr]) hfin
  have hzinj : Function.Injective z' := by
    have h : (Finset.image z' Finset.univ).card = (Finset.univ : Finset (Fin e)).card := by
      rw [← Set.ncard_coe_finset (Finset.image z' Finset.univ), Finset.coe_image, Finset.coe_univ,
        Set.image_univ, hnr, Finset.card_univ, Fintype.card_fin]
    have h' := Finset.card_image_iff.mp h
    rwa [Finset.coe_univ, Set.injOn_univ] at h'
  subst hteq
  exact (algebraicIndependent_subtype_range hzinj).mp htb.1

end StrictDrop

section Le

theorem trdeg_le_of_generated {k₀ E₀ L₀ T : Type u} [CommRing k₀] [IsDomain k₀] [CommRing E₀]
    [CommRing L₀]
    [IsDomain L₀] [CommRing T] [IsDomain T] [Algebra k₀ E₀] [Algebra k₀ L₀] [FaithfulSMul k₀ L₀]
        [Algebra E₀ T]
    [Algebra k₀ T] [IsScalarTower k₀ E₀ T] (ι : L₀ →ₐ[k₀] T) (hι : Function.Injective ι)
    (hgen : ∀ t : T, t ∈ Algebra.adjoin E₀ (Set.range ι)) :
    Algebra.trdeg E₀ T ≤ Algebra.trdeg k₀ L₀ := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k₀ L₀
  let K₁ : Subalgebra k₀ L₀ := Algebra.adjoin k₀ s
  let K₂ : Subalgebra k₀ T := K₁.map ι
  let D₁ : Subalgebra E₀ T := Algebra.adjoin E₀ (ι '' s)
  have hK : Algebra.IsAlgebraic K₁ L₀ := by
    have h := hs.isAlgebraic
    rwa [Subtype.range_coe_subtype, Set.ofPred_mem_eq] at h
  have hA1 : ∀ ℓ : L₀, IsAlgebraic K₂ (ι ℓ) := by
    intro ℓ
    exact (hK.isAlgebraic ℓ).ringHom_of_comp_eq (ι.subalgebraMap K₁) ι
      (fun x y hxy => Subtype.ext (hι (congrArg (fun z : K₂ => (z : T)) hxy))) (RingHom.ext fun _
          => rfl)
  have hK₂D₁ : K₂ ≤ D₁.restrictScalars k₀ := by
    change K₁.map ι ≤ _
    rw [AlgHom.map_adjoin]
    refine Algebra.adjoin_le fun x hx => ?_
    exact (Subalgebra.mem_restrictScalars k₀).mpr (Algebra.subset_adjoin hx)
  have hA1' : ∀ ℓ : L₀, IsAlgebraic D₁ (ι ℓ) := by
    intro ℓ
    exact (hA1 ℓ).ringHom_of_comp_eq (Subalgebra.inclusion hK₂D₁) (RingHom.id T)
      (Subalgebra.inclusion_injective hK₂D₁) (RingHom.ext fun _ => rfl)
  have hadj : ∀ x ∈ Algebra.adjoin D₁ (Set.range ι), IsAlgebraic D₁ x :=
    Algebra.isAlgebraic_adjoin_iff.mpr (by rintro _ ⟨ℓ, rfl⟩; exact hA1' ℓ)
  have hle : ∀ x : T, x ∈ Algebra.adjoin E₀ (Set.range ι) → x ∈ Algebra.adjoin D₁ (Set.range ι)
      := by
    intro x hx
    refine Algebra.adjoin_induction (hx := hx) ?_ ?_ ?_ ?_
    · intro y hy; exact Algebra.subset_adjoin hy
    · intro e
      have : algebraMap E₀ T e = algebraMap D₁ T (algebraMap E₀ D₁ e) := rfl
      rw [this]; exact Subalgebra.algebraMap_mem _ _
    · intro _ _ _ _ hx hy; exact Subalgebra.add_mem _ hx hy
    · intro _ _ _ _ hx hy; exact Subalgebra.mul_mem _ hx hy
  have : Algebra.IsAlgebraic D₁ T := ⟨fun t => hadj t (hle t (hgen t))⟩
  calc Algebra.trdeg E₀ T ≤ Cardinal.mk (ι '' s) := Algebra.IsAlgebraic.trdeg_le_cardinalMk E₀ (ι
      '' s)
    _ ≤ Cardinal.mk s := Cardinal.mk_image_le
    _ = Algebra.trdeg k₀ L₀ := hs.cardinalMk_eq_trdeg

variable {R A A' : Type u} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']

theorem includeRight_algebraMap (r : R) :
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom (algebraMap R A' r) =
      algebraMap R (A ⊗[R] A') r :=
  (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).commutes r

theorem trdeg_le (𝔓 : Ideal (A ⊗[R] A')) [𝔓.IsPrime] (𝔭 : Ideal A) [𝔭.IsPrime] [𝔓.LiesOver 𝔭]
    (𝔭' : Ideal A') [𝔭'.IsPrime]
    (h𝔭' : 𝔭' = 𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom)
    (𝔫 : Ideal R) [𝔫.IsPrime] [𝔭'.LiesOver 𝔫] [𝔭.LiesOver 𝔫] :
    Algebra.trdeg (A ⧸ 𝔭) ((A ⊗[R] A') ⧸ 𝔓) ≤ Algebra.trdeg (R ⧸ 𝔫) (A' ⧸ 𝔭') := by
  classical
  let inR : A' →+* A ⊗[R] A' := (Algebra.TensorProduct.includeRight (R := R) (A := A) (B :=
      A')).toRingHom
  have hPn : (𝔓 : Ideal (A ⊗[R] A')).LiesOver 𝔫 := by
    constructor
    rw [Ideal.LiesOver.over (P := 𝔭) (p := 𝔫), Ideal.LiesOver.over (P := 𝔓) (p := 𝔭),
        Ideal.under_under]
  have : IsScalarTower (R ⧸ 𝔫) (A ⧸ 𝔭) ((A ⊗[R] A') ⧸ 𝔓) := by
    refine IsScalarTower.of_algebraMap_eq fun κ => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective κ
    rfl
  let ιLT : A' ⧸ 𝔭' →+* (A ⊗[R] A') ⧸ 𝔓 := Ideal.quotientMap 𝔓 inR (le_of_eq h𝔭')
  have hιLT : ∀ a' : A', ιLT (Ideal.Quotient.mk 𝔭' a') = Ideal.Quotient.mk 𝔓 (inR a') := fun _ =>
      rfl
  have hιLT_inj : Function.Injective ιLT := Ideal.quotientMap_injective' (le_of_eq h𝔭'.symm)
  have hcompat : ∀ κ : R ⧸ 𝔫, ιLT (algebraMap (R ⧸ 𝔫) (A' ⧸ 𝔭') κ) =
      (algebraMap (R ⧸ 𝔫) ((A ⊗[R] A') ⧸ 𝔓) : (R ⧸ 𝔫) →+* ((A ⊗[R] A') ⧸ 𝔓)) κ := by
    intro κ
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective κ
    change ιLT (Ideal.Quotient.mk 𝔭' (algebraMap R A' r)) = Ideal.Quotient.mk 𝔓 (algebraMap R (A
        ⊗[R] A') r)
    rw [hιLT, includeRight_algebraMap]
  let ιLTₐ : (A' ⧸ 𝔭') →ₐ[R ⧸ 𝔫] ((A ⊗[R] A') ⧸ 𝔓) := { ιLT with commutes' := hcompat }
  refine trdeg_le_of_generated ιLTₐ hιLT_inj fun t => ?_
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective t
  induction b using TensorProduct.inductionOn with
  | tmul a a' =>
    have h1 : a ⊗ₜ[R] a' = algebraMap A (A ⊗[R] A') a * inR a' := by
      change a ⊗ₜ[R] a' = (a ⊗ₜ[R] 1) * ((1 : A) ⊗ₜ[R] a')
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h1, map_mul]
    refine Subalgebra.mul_mem _ ?_ (Algebra.subset_adjoin ⟨Ideal.Quotient.mk 𝔭' a', hιLT a'⟩)
    exact Subalgebra.algebraMap_mem (Algebra.adjoin (A ⧸ 𝔭) (Set.range ιLTₐ)) (Ideal.Quotient.mk 𝔭
        a)
  | add x y hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy

end Le

section GoingDown

theorem flat_of_faithfulSMul_field (K' L : Type u) [CommRing K'] [IsDomain K'] [Field L] [Algebra
    K' L]
    [FaithfulSMul K' L] : Module.Flat K' L := by
  let : Algebra (FractionRing K') L :=
    (IsFractionRing.lift (FaithfulSMul.algebraMap_injective K' L)).toAlgebra
  have : IsScalarTower K' (FractionRing K') L :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective K' L) x).symm
  have : Module.Flat K' (FractionRing K') := IsLocalization.flat (FractionRing K') (nonZeroDivisors
      K')
  exact Module.Flat.trans K' (FractionRing K') L

theorem under_eq_bot_of_forall {S' D : Type u} [CommRing S'] [IsDomain S'] [CommRing D] [Algebra S'
    D]
    [Algebra.HasGoingDown S' D] (P₂ : Ideal D) [P₂.IsPrime]
    (hmin : ∀ P' : Ideal D, P'.IsPrime → P' ≤ P₂ → P'.under S' = ⊥ → P' = P₂) : P₂.under S' = ⊥
        := by
  by_contra h
  have hlt : (⊥ : Ideal S') < P₂.under S' := bot_lt_iff_ne_bot.mpr h
  obtain ⟨P', hP', hP'prime, hP'over⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := (⊥ : Ideal S'))
    (q := P₂.under S') P₂ hlt
  have h1 : P'.under S' = ⊥ := (hP'over.over).symm
  exact (ne_of_lt hP') (hmin P' hP'prime hP'.le h1)

end GoingDown

section Ge

variable {R A A' : Type u} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']

theorem le_trdeg_of_mem_minimalPrimes [Algebra.FiniteType R A']
    (𝔓 : Ideal (A ⊗[R] A')) [𝔓.IsPrime] (𝔭 : Ideal A) [𝔭.IsPrime] [𝔓.LiesOver 𝔭]
    (𝔭' : Ideal A') [𝔭'.IsPrime]
    (h𝔭' : 𝔭' = 𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom)
    (𝔫 : Ideal R) [𝔫.IsPrime] [𝔭'.LiesOver 𝔫] [𝔭.LiesOver 𝔫]
    (hmin : 𝔓 ∈ ((𝔭.map (algebraMap A (A ⊗[R] A'))).minimalPrimes)) :
    Algebra.trdeg (R ⧸ 𝔫) (A' ⧸ 𝔭') ≤ Algebra.trdeg (A ⧸ 𝔭) ((A ⊗[R] A') ⧸ 𝔓) := by
  classical
  let inR : A' →+* A ⊗[R] A' := (Algebra.TensorProduct.includeRight (R := R) (A := A) (B :=
      A')).toRingHom
  have hinR : ∀ a', inR a' = (1 : A) ⊗ₜ[R] a' := fun _ => rfl
  have : Algebra.FiniteType (R ⧸ 𝔫) (A' ⧸ 𝔭') := by
    have h : 𝔫 = 𝔭'.under R := Ideal.LiesOver.over
    subst h
    infer_instance
  obtain ⟨r₀, hr₀, d, w, hw, hint⟩ :=
    Algebra.exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType
      (R := R ⧸ 𝔫) (C := A' ⧸ 𝔭')
  have halgL : Algebra.IsAlgebraic (Algebra.adjoin (R ⧸ 𝔫) (Set.range w)) (A' ⧸ 𝔭') := by
    have h := isAlgebraic_quotient_of_noether (E₀ := R ⧸ 𝔫) (E₀' := R ⧸ 𝔫) (C := A' ⧸ 𝔭') (C' := A'
        ⧸ 𝔭')
      (RingHom.id _) (RingHom.id _) (fun _ => rfl) Function.surjective_id w r₀ hr₀ hint
    exact ⟨fun x => h x trivial⟩
  have hbasis : IsTranscendenceBasis (R ⧸ 𝔫) w := hw.isTranscendenceBasis_iff_isAlgebraic.mpr halgL
  have hd : (d : Cardinal.{u}) = Algebra.trdeg (R ⧸ 𝔫) (A' ⧸ 𝔭') := by
    have h := hbasis.lift_cardinalMk_eq_trdeg
    simpa only [Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_uzero] using h
  rw [← hd]
  let K' := MvPolynomial (Fin d) (R ⧸ 𝔫)
  let S' := MvPolynomial (Fin d) (A ⧸ 𝔭)
  let L := 𝔭'.ResidueField
  let jS : K' →+* S' := MvPolynomial.map (algebraMap (R ⧸ 𝔫) (A ⧸ 𝔭))
  let jL : K' →+* L := (algebraMap (A' ⧸ 𝔭') L).comp (MvPolynomial.aeval w).toRingHom
  have hjL_inj : Function.Injective jL :=
    (IsFractionRing.injective (A' ⧸ 𝔭') L).comp (algebraicIndependent_iff_injective_aeval.mp hw)
  let algKS : Algebra K' S' := jS.toAlgebra
  let algKL : Algebra K' L := jL.toAlgebra
  have : FaithfulSMul K' L := (faithfulSMul_iff_algebraMap_injective K' L).mpr hjL_inj
  have : Module.Flat K' L := flat_of_faithfulSMul_field K' L
  have : Module.Flat S' (S' ⊗[K'] L) := inferInstance
  have : Algebra.HasGoingDown S' (S' ⊗[K'] L) := inferInstance
  let φBΩ : (A ⊗[R] A') →+* 𝔓.ResidueField := algebraMap (A ⊗[R] A') 𝔓.ResidueField
  let φTΩ := Ideal.Quotient.lift 𝔓 φBΩ (fun b hb => Ideal.algebraMap_residueField_eq_zero.mpr hb)
  have hφTΩ : ∀ b, φTΩ (Ideal.Quotient.mk 𝔓 b) = φBΩ b := fun _ => rfl
  let φE : (A ⧸ 𝔭) →+* 𝔓.ResidueField := Ideal.Quotient.lift 𝔭 (φBΩ.comp (algebraMap A (A ⊗[R] A')))
    (fun a ha => by
      rw [RingHom.comp_apply]
      apply Ideal.algebraMap_residueField_eq_zero.mpr
      change a ∈ 𝔓.under A
      rw [← Ideal.LiesOver.over (P := 𝔓) (p := 𝔭)]
      exact ha)
  have hφE : ∀ a : A, φE (Ideal.Quotient.mk 𝔭 a) = φBΩ (algebraMap A (A ⊗[R] A') a) := fun _ => rfl
  let φL : L →+* 𝔓.ResidueField := Ideal.ResidueField.map 𝔭' 𝔓 inR h𝔭'
  have hφL : ∀ a' : A', φL (algebraMap (A' ⧸ 𝔭') L (Ideal.Quotient.mk 𝔭' a')) = φBΩ (inR a') := by
    intro a'
    exact Ideal.ResidueField.map_algebraMap 𝔭' 𝔓 inR h𝔭' a'
  choose wt hwt using fun i => Ideal.Quotient.mk_surjective (I := 𝔭') (w i)
  let ω : Fin d → 𝔓.ResidueField := fun i => φBΩ (inR (wt i))
  let φS : S' →+* 𝔓.ResidueField := MvPolynomial.eval₂Hom φE ω
  have hRR : ∀ r : R, φE (algebraMap (R ⧸ 𝔫) (A ⧸ 𝔭) (Ideal.Quotient.mk 𝔫 r)) =
      φL (algebraMap (A' ⧸ 𝔭') L (algebraMap (R ⧸ 𝔫) (A' ⧸ 𝔭') (Ideal.Quotient.mk 𝔫 r))) := by
    intro r
    change φE (Ideal.Quotient.mk 𝔭 (algebraMap R A r)) =
      φL (algebraMap (A' ⧸ 𝔭') L (Ideal.Quotient.mk 𝔭' (algebraMap R A' r)))
    rw [hφE, hφL, includeRight_algebraMap]
    rfl
  have hSK : φS.comp jS = φL.comp jL := by
    apply MvPolynomial.ringHom_ext
    · intro κ
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective κ
      change φS (MvPolynomial.map _ (MvPolynomial.C _)) = φL (algebraMap (A' ⧸ 𝔭') L
          (MvPolynomial.aeval w (MvPolynomial.C _)))
      rw [MvPolynomial.map_C, MvPolynomial.algHom_C]
      change (MvPolynomial.eval₂Hom φE ω) (MvPolynomial.C _) = _
      rw [MvPolynomial.eval₂Hom_C]
      exact hRR r
    · intro i
      change φS (MvPolynomial.map _ (MvPolynomial.X i)) = φL (algebraMap (A' ⧸ 𝔭') L
          (MvPolynomial.aeval w (MvPolynomial.X i)))
      rw [MvPolynomial.map_X, MvPolynomial.aeval_X, ← hwt i, hφL]
      exact MvPolynomial.eval₂Hom_X' φE ω i
  let algKΩ : Algebra K' 𝔓.ResidueField := (φS.comp jS).toAlgebra
  let φSₐ : S' →ₐ[K'] 𝔓.ResidueField := { φS with commutes' := fun _ => rfl }
  let φLₐ : L →ₐ[K'] 𝔓.ResidueField :=
    { φL with commutes' := fun κ => (RingHom.congr_fun hSK κ).symm }
  let Φ : S' ⊗[K'] L →ₐ[K'] 𝔓.ResidueField := Algebra.TensorProduct.lift φSₐ φLₐ (fun _ _ =>
      Commute.all _ _)
  have hΦ : ∀ (x : S') (y : L), Φ (x ⊗ₜ[K'] y) = φS x * φL y := fun x y =>
      Algebra.TensorProduct.lift_tmul _ _ _ x y
  let P₂ : Ideal (S' ⊗[K'] L) := RingHom.ker Φ.toRingHom
  have : P₂.IsPrime := RingHom.ker_isPrime _
  have : SMulCommClass K' R S' := ⟨fun κ r x => by simp only [Algebra.smul_def]; ring⟩
  let iS : S' →+* S' ⊗[K'] L := algebraMap S' (S' ⊗[K'] L)
  have hiS : ∀ x, iS x = x ⊗ₜ[K'] (1 : L) := fun _ => rfl
  let iL : L →+* S' ⊗[K'] L := (Algebra.TensorProduct.includeRight (R := K') (A := S') (B :=
      L)).toRingHom
  have hiL : ∀ y, iL y = (1 : S') ⊗ₜ[K'] y := fun _ => rfl
  let ψA₀ : A →+* S' ⊗[K'] L := iS.comp (MvPolynomial.C.comp (Ideal.Quotient.mk 𝔭))
  let ψA'₀ : A' →+* S' ⊗[K'] L := iL.comp ((algebraMap (A' ⧸ 𝔭') L).comp (Ideal.Quotient.mk 𝔭'))
  have hKtmul : ∀ κ : K', (jS κ) ⊗ₜ[K'] (1 : L) = (1 : S') ⊗ₜ[K'] (jL κ) := by
    intro κ
    have h1 : jS κ = κ • (1 : S') := by rw [Algebra.smul_def, mul_one]; rfl
    have h2 : jL κ = κ • (1 : L) := by rw [Algebra.smul_def, mul_one]; rfl
    rw [h1, h2, TensorProduct.smul_tmul]
  have hRD : ∀ r : R, ψA₀ (algebraMap R A r) = ψA'₀ (algebraMap R A' r) := by
    intro r
    change iS (MvPolynomial.C (Ideal.Quotient.mk 𝔭 (algebraMap R A r))) =
      iL (algebraMap (A' ⧸ 𝔭') L (Ideal.Quotient.mk 𝔭' (algebraMap R A' r)))
    have h1 : MvPolynomial.C (Ideal.Quotient.mk 𝔭 (algebraMap R A r)) = jS (MvPolynomial.C
        (Ideal.Quotient.mk 𝔫 r)) := by
      rw [MvPolynomial.map_C]; rfl
    have h2 : algebraMap (A' ⧸ 𝔭') L (Ideal.Quotient.mk 𝔭' (algebraMap R A' r)) =
        jL (MvPolynomial.C (Ideal.Quotient.mk 𝔫 r)) := by
      change _ = algebraMap (A' ⧸ 𝔭') L (MvPolynomial.aeval w (MvPolynomial.C _))
      rw [MvPolynomial.algHom_C]; rfl
    rw [h1, h2, hiS, hiL, hKtmul]
  have hψA₀R : ∀ r : R, ψA₀ (algebraMap R A r) = algebraMap R (S' ⊗[K'] L) r := by
    intro r
    rw [Algebra.TensorProduct.algebraMap_apply]
    rfl
  let ψAₐ : A →ₐ[R] S' ⊗[K'] L := { ψA₀ with commutes' := hψA₀R }
  let ψA'ₐ : A' →ₐ[R] S' ⊗[K'] L := { ψA'₀ with commutes' := fun r => by rw [← hψA₀R, hRD]; rfl }
  let ψ : A ⊗[R] A' →+* S' ⊗[K'] L :=
    (Algebra.TensorProduct.lift ψAₐ ψA'ₐ (fun _ _ => Commute.all _ _)).toRingHom
  have hψ : ∀ (a : A) (a' : A'), ψ (a ⊗ₜ[R] a') = ψA₀ a * ψA'₀ a' := fun a a' =>
    Algebra.TensorProduct.lift_tmul ψAₐ ψA'ₐ _ a a'
  have hψinR : ∀ a', ψ (inR a') = ψA'₀ a' := by
    intro a'; rw [hinR, hψ, map_one, one_mul]
  have hψA : ∀ a, ψ (algebraMap A (A ⊗[R] A') a) = ψA₀ a := by
    intro a
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hψ,
        map_one, mul_one]
  have hΦψA : ∀ a : A, Φ (ψA₀ a) = φBΩ (algebraMap A (A ⊗[R] A') a) := by
    intro a
    change Φ ((MvPolynomial.C (Ideal.Quotient.mk 𝔭 a)) ⊗ₜ[K'] (1 : L)) = _
    rw [hΦ, map_one, mul_one, ← hφE]
    exact MvPolynomial.eval₂Hom_C φE ω _
  have hΦψA' : ∀ a' : A', Φ (ψA'₀ a') = φBΩ (inR a') := by
    intro a'
    change Φ ((1 : S') ⊗ₜ[K'] (algebraMap (A' ⧸ 𝔭') L (Ideal.Quotient.mk 𝔭' a'))) = _
    rw [hΦ, map_one, one_mul, hφL]
  have hΦψ : ∀ b : A ⊗[R] A', Φ (ψ b) = φBΩ b := by
    intro b
    induction b using TensorProduct.inductionOn with
    | tmul a a' =>
      rw [hψ, map_mul, hΦψA, hΦψA', ← map_mul]
      congr 1
      rw [hinR, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have hcomapP₂ : P₂.comap ψ = 𝔓 := by
    ext b
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change Φ (ψ b) = 0 ↔ b ∈ 𝔓
    rw [hΦψ]
    exact Ideal.algebraMap_residueField_eq_zero
  have hden : ∀ z : S' ⊗[K'] L, ∃ σ : A', σ ∉ 𝔭' ∧ ∃ b : A ⊗[R] A', ψA'₀ σ * z = ψ b := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x ℓ =>
      obtain ⟨num, den, hden, hℓ⟩ := IsFractionRing.div_surjective (A := A' ⧸ 𝔭') ℓ
      obtain ⟨a₁, rfl⟩ := Ideal.Quotient.mk_surjective num
      obtain ⟨σ, rfl⟩ := Ideal.Quotient.mk_surjective den
      have hσ : σ ∉ 𝔭' := fun h => by
        have : (Ideal.Quotient.mk 𝔭' σ) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
        rw [this] at hden
        exact zero_notMem_nonZeroDivisors hden
      have hσ0 : algebraMap (A' ⧸ 𝔭') L (Ideal.Quotient.mk 𝔭' σ) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hden
      have hx : ∃ b : A ⊗[R] A', x ⊗ₜ[K'] (algebraMap (A' ⧸ 𝔭') L (Ideal.Quotient.mk 𝔭' a₁)) = ψ b
          := by
        induction x using MvPolynomial.induction_on with
        | C e =>
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
          refine ⟨a ⊗ₜ[R] a₁, ?_⟩
          rw [hψ]
          change _ = iS (MvPolynomial.C (Ideal.Quotient.mk 𝔭 a)) *
            iL (algebraMap (A' ⧸ 𝔭') L (Ideal.Quotient.mk 𝔭' a₁))
          rw [hiS, hiL, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        | add p q hp hq =>
          obtain ⟨b₁, hb₁⟩ := hp
          obtain ⟨b₂, hb₂⟩ := hq
          exact ⟨b₁ + b₂, by rw [TensorProduct.add_tmul, hb₁, hb₂, map_add]⟩
        | mul_X p i hp =>
          obtain ⟨b, hb⟩ := hp
          refine ⟨b * inR (wt i), ?_⟩
          have hX : (MvPolynomial.X i : S') ⊗ₜ[K'] (1 : L) = ψ (inR (wt i)) := by
            rw [hψinR]
            change _ = iL (algebraMap (A' ⧸ 𝔭') L (Ideal.Quotient.mk 𝔭' (wt i)))
            rw [hiL, hwt i]
            have h1 : (MvPolynomial.X i : S') = jS (MvPolynomial.X i) := (MvPolynomial.map_X _
                i).symm
            have h2 : algebraMap (A' ⧸ 𝔭') L (w i) = jL (MvPolynomial.X i) := by
              change _ = algebraMap (A' ⧸ 𝔭') L (MvPolynomial.aeval w (MvPolynomial.X i))
              rw [MvPolynomial.aeval_X]
            rw [h1, h2, hKtmul]
          rw [map_mul, ← hb, ← hX, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      obtain ⟨b, hb⟩ := hx
      refine ⟨σ, hσ, b, ?_⟩
      change iL (algebraMap (A' ⧸ 𝔭') L (Ideal.Quotient.mk 𝔭' σ)) * (x ⊗ₜ[K'] ℓ) = ψ b
      rw [hiL, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hb, ← hℓ, mul_div_cancel₀ _ hσ0]
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨σ₁, hσ₁, b₁, hb₁⟩ := h₁
      obtain ⟨σ₂, hσ₂, b₂, hb₂⟩ := h₂
      refine ⟨σ₁ * σ₂, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hσ₁ hσ₂,
        inR σ₂ * b₁ + inR σ₁ * b₂, ?_⟩
      rw [map_mul, mul_add, map_add, map_mul, map_mul, hψinR, hψinR, ← hb₁, ← hb₂]
      ring
  have hmin' : ∀ P' : Ideal (S' ⊗[K'] L), P'.IsPrime → P' ≤ P₂ → P'.under S' = ⊥ → P' = P₂ := by
    intro P' hP' hle _
    have hQ : P'.comap ψ = 𝔓 := by
      apply le_antisymm
      · rw [← hcomapP₂]; exact Ideal.comap_mono hle
      · refine hmin.2 ⟨Ideal.comap_isPrime ψ P', ?_⟩ (by
          rw [← hcomapP₂]
          exact Ideal.comap_mono hle)
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, Ideal.mem_comap, hψA]
        change iS (MvPolynomial.C (Ideal.Quotient.mk 𝔭 a)) ∈ P'
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero, map_zero]
        exact P'.zero_mem
    apply le_antisymm hle
    intro z hz
    obtain ⟨σ, hσ, b, hb⟩ := hden z
    have hb₂ : ψ b ∈ P₂ := by rw [← hb]; exact P₂.mul_mem_left _ hz
    have hb𝔓 : b ∈ 𝔓 := by rw [← hcomapP₂]; exact hb₂
    have hb' : ψ b ∈ P' := by
      have : b ∈ P'.comap ψ := by rw [hQ]; exact hb𝔓
      exact this
    rw [← hb] at hb'
    rcases hP'.mem_or_mem hb' with h | h
    · exfalso
      apply hσ
      rw [← hψinR] at h
      have : inR σ ∈ P'.comap ψ := h
      rw [hQ] at this
      rw [h𝔭']; exact this
    · exact h
  have hP₂S : P₂.under S' = ⊥ := under_eq_bot_of_forall (S' := S') (D := S' ⊗[K'] L) P₂ hmin'
  have hφS : φS = Φ.toRingHom.comp iS := by
    ext x
    · change φS (MvPolynomial.C x) = Φ ((MvPolynomial.C x) ⊗ₜ[K'] (1 : L))
      rw [hΦ, map_one, mul_one]
    · change φS (MvPolynomial.X _) = Φ ((MvPolynomial.X _) ⊗ₜ[K'] (1 : L))
      rw [hΦ, map_one, mul_one]
  have hφS_inj : Function.Injective φS := by
    rw [RingHom.injective_iff_ker_eq_bot, hφS, ← RingHom.comap_ker]
    exact hP₂S
  have haeval : ∀ q : S', φTΩ (MvPolynomial.aeval (R := A ⧸ 𝔭)
      (fun i => Ideal.Quotient.mk 𝔓 (inR (wt i))) q) = φS q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C e =>
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
      rw [MvPolynomial.algHom_C]
      change φTΩ (Ideal.Quotient.mk 𝔓 (algebraMap A (A ⊗[R] A') a)) = (MvPolynomial.eval₂Hom φE ω)
          (MvPolynomial.C _)
      rw [MvPolynomial.eval₂Hom_C, hφTΩ, hφE]
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | mul_X p i hp =>
      rw [map_mul, map_mul, hp, map_mul, MvPolynomial.aeval_X, hφTΩ]
      congr 1
      exact (MvPolynomial.eval₂Hom_X' φE ω i).symm
  have hind : AlgebraicIndependent (A ⧸ 𝔭) (fun i => Ideal.Quotient.mk 𝔓 (inR (wt i))) := by
    rw [algebraicIndependent_iff]
    intro q hq
    apply hφS_inj
    rw [← haeval, hq, map_zero, map_zero]
  simpa only [Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_uzero] using
    hind.lift_cardinalMk_le_trdeg

end Ge

section Main

variable {R A A' : Type u} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']

theorem comap_includeRight_under (Q : Ideal (A ⊗[R] A')) :
    (Q.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom).under R =
        Q.under R := by
  rw [Ideal.under, Ideal.under, Ideal.comap_comap]
  congr 1
  ext r
  exact includeRight_algebraMap r

theorem main [Algebra.FiniteType R A']
    (𝔓 : Ideal (A ⊗[R] A')) [𝔓.IsPrime]
    (h : 𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom ∈
      ((𝔓.under R).map (algebraMap R A')).minimalPrimes) :
    Algebra.trdeg (A ⧸ 𝔓.under A) ((A ⊗[R] A') ⧸ 𝔓) ≤
        Algebra.trdeg
          (R ⧸ (𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B :=
              A')).toRingHom).under R)
          (A' ⧸ 𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom)
              ∧
      (𝔓 ∈ ((𝔓.under A).map (algebraMap A (A ⊗[R] A'))).minimalPrimes ↔
        Algebra.trdeg (A ⧸ 𝔓.under A) ((A ⊗[R] A') ⧸ 𝔓) =
          Algebra.trdeg
            (R ⧸ (𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B :=
                A')).toRingHom).under R)
            (A' ⧸ 𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B :=
                A')).toRingHom)) := by
  classical
  set inR := (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom with hinR
  set 𝔭 : Ideal A := 𝔓.under A with h𝔭
  set 𝔭' : Ideal A' := 𝔓.comap inR with h𝔭'def
  set 𝔫 : Ideal R := 𝔭'.under R with h𝔫
  have : Algebra.FiniteType A (A ⊗[R] A') := Algebra.FiniteType.baseChange (R := R) (A := A') A
  have h𝔫R : 𝔫 = 𝔓.under R := comap_includeRight_under 𝔓
  have : 𝔭.LiesOver 𝔫 := ⟨by rw [h𝔫R, h𝔭, Ideal.under_under]⟩
  have hle : Algebra.trdeg (A ⧸ 𝔭) ((A ⊗[R] A') ⧸ 𝔓) ≤ Algebra.trdeg (R ⧸ 𝔫) (A' ⧸ 𝔭') :=
    trdeg_le 𝔓 𝔭 𝔭' rfl 𝔫
  refine ⟨hle, ⟨fun hmin => le_antisymm hle (le_trdeg_of_mem_minimalPrimes 𝔓 𝔭 𝔭' rfl 𝔫 hmin), fun
      heq => ?_⟩⟩
  by_contra hnot
  obtain ⟨Q, hQmin, hQle⟩ := Ideal.exists_minimalPrimes_le (I := 𝔭.map (algebraMap A (A ⊗[R] A')))
      (J := 𝔓)
    (Ideal.map_le_iff_le_comap.mpr le_rfl)
  have hQprime : Q.IsPrime := hQmin.1.1
  have hQne : Q ≠ 𝔓 := by
    rintro rfl
    exact hnot hQmin
  have hlt : Q < 𝔓 := lt_of_le_of_ne hQle hQne
  have hQA : Q.under A = 𝔭 :=
    le_antisymm (h𝔭 ▸ Ideal.comap_mono hQle) (Ideal.map_le_iff_le_comap.mp hQmin.1.2)
  have : Q.LiesOver 𝔭 := ⟨hQA.symm⟩
  have hQ𝔭' : 𝔭' = Q.comap inR := by
    have hle' : Q.comap inR ≤ 𝔭' := Ideal.comap_mono hQle
    refine le_antisymm (h.2 ⟨Ideal.comap_isPrime inR Q, ?_⟩ hle') hle'
    rw [Ideal.map_le_iff_le_comap]
    change 𝔓.under R ≤ (Q.comap inR).under R
    rw [comap_includeRight_under Q, ← Ideal.under_under (B := A) Q, hQA, h𝔭, Ideal.under_under]
  have hleQ : Algebra.trdeg (A ⧸ 𝔭) ((A ⊗[R] A') ⧸ Q) ≤ Algebra.trdeg (R ⧸ 𝔫) (A' ⧸ 𝔭') :=
    trdeg_le Q 𝔭 𝔭' hQ𝔭' 𝔫
  have hstrict := trdeg_quotient_lt_of_lt 𝔭 Q 𝔓 hlt
  exact absurd heq (ne_of_lt (lt_of_lt_of_le hstrict hleQ))

end Main

end TensorPrimes

with_weak_namespace _root_.Algebra.TensorProduct
theorem trdeg_quotient_le_and_mem_minimalPrimes_iff_of_mem_minimalPrimes
    {R A A' : Type u} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    [Algebra.FiniteType R A']
    (𝔓 : Ideal (A ⊗[R] A')) [𝔓.IsPrime]
    (h : 𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom ∈
      ((𝔓.under R).map (algebraMap R A')).minimalPrimes) :
    Algebra.trdeg (A ⧸ 𝔓.under A) ((A ⊗[R] A') ⧸ 𝔓) ≤
        Algebra.trdeg
          (R ⧸ (𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B :=
              A')).toRingHom).under R)
          (A' ⧸ 𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom)
              ∧
      (𝔓 ∈ ((𝔓.under A).map (algebraMap A (A ⊗[R] A'))).minimalPrimes ↔
        Algebra.trdeg (A ⧸ 𝔓.under A) ((A ⊗[R] A') ⧸ 𝔓) =
          Algebra.trdeg
            (R ⧸ (𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B :=
                A')).toRingHom).under R)
            (A' ⧸ 𝔓.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B :=
                A')).toRingHom)) :=
  AbelianVarieties.NOSProofs.TensorTranscendence.TensorPrimes.main 𝔓 h

end TensorTranscendence
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_IsIntegral_ringKrullDim_le_of_injective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace IntegralDimension
theorem _root_.Algebra.IsIntegral.ringKrullDim_le_of_injective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R ≤ ringKrullDim S := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [ringKrullDim_eq_bot_of_subsingleton]; exact bot_le
  have : Nontrivial S := hinj.nontrivial
  have hbot : ∀ P : Ideal R, (⊥ : Ideal S).comap (algebraMap R S) ≤ P := by
    intro P x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    have : x = 0 := hinj (by rw [hx, map_zero])
    rw [this]; exact zero_mem _
  have key : ∀ n : ℕ, ∀ l : LTSeries (PrimeSpectrum R), l.length = n →
      ∃ l' : LTSeries (PrimeSpectrum S), l'.length = n ∧
        l'.last.asIdeal.comap (algebraMap R S) = l.last.asIdeal := by
    intro n
    induction n with
    | zero =>
      intro l hl
      obtain ⟨Q, -, hQ, hQc⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral l.last.asIdeal (⊥ : Ideal S) (hbot _)
      exact ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, by simpa only [RelSeries.last_singleton] using hQc⟩
    | succ n ih =>
      intro l hl
      have hne : l.length ≠ 0 := by omega
      obtain ⟨l'', hl'', hc⟩ := ih l.eraseLast (by simp only [RelSeries.eraseLast_length, hl,
          Nat.add_sub_cancel])
      have hrel : l.eraseLast.last < l.last := l.eraseLast_last_rel_last hne
      obtain ⟨Q, hQge, hQ, hQc⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral l.last.asIdeal l''.last.asIdeal
          (by
            rw [Ideal.under_def, hc]
            exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hrel.le)
      have hlt : l''.last < ⟨Q, hQ⟩ := by
        refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hQge) ?_
        intro heq
        have h1 : l''.last.asIdeal = Q := by rw [heq]
        have h2 : l.eraseLast.last.asIdeal = l.last.asIdeal := by rw [← hc, ← hQc, h1]
        exact (ne_of_lt hrel) (PrimeSpectrum.ext h2)
      refine ⟨l''.snoc ⟨Q, hQ⟩ hlt, by rw [RelSeries.snoc_length, hl''], ?_⟩
      simpa only [RelSeries.last_snoc] using hQc
  rw [ringKrullDim, ringKrullDim, Order.krullDim_eq_iSup_length, Order.krullDim_eq_iSup_length]
  refine WithBot.coe_le_coe.mpr (iSup_le fun l => ?_)
  obtain ⟨l', hl', -⟩ := key l.length l rfl
  exact le_iSup_of_le l' (by rw [hl'])

end IntegralDimension
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace FiniteTypeDimension
universe u v

namespace Algebra
open _root_.Algebra
namespace RingKrullDimEqTrdeg
open _root_.Algebra

open Cardinal

theorem exists_ltSeries_comap_eq_last {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ L : LTSeries (PrimeSpectrum S), L.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R S) L.last = l.last := by
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨q, hq⟩ := Algebra.IsIntegral.comap_surjective R S x
    exact ⟨RelSeries.singleton _ q, rfl, hq⟩
  | snoc l x hx ih =>
    obtain ⟨L, hlen, hlast⟩ := ih
    have hle : L.last.asIdeal.comap (algebraMap R S) ≤ x.asIdeal := by
      have h1 : PrimeSpectrum.comap (algebraMap R S) L.last ≤ x := hlast ▸ le_of_lt hx
      exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr h1
    obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal L.last.asIdeal hle
    have hlx : l.last < x := hx
    have hQlt : L.last < (⟨Q, hQprime⟩ : PrimeSpectrum S) := by
      refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hQge) ?_
      intro h
      refine absurd ?_ (ne_of_lt hlx)
      calc l.last = PrimeSpectrum.comap (algebraMap R S) L.last := hlast.symm
        _ = PrimeSpectrum.comap (algebraMap R S) ⟨Q, hQprime⟩ := by rw [h]
        _ = x := PrimeSpectrum.ext hQcomap
    refine ⟨L.snoc ⟨Q, hQprime⟩ hQlt, by simp only [RelSeries.snoc_length, hlen], ?_⟩
    simp only [RelSeries.last_snoc]
    exact PrimeSpectrum.ext hQcomap

theorem ringKrullDim_eq_of_isIntegral_of_injective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R = ringKrullDim S := by
  refine le_antisymm ?_ ?_
  · change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
    refine iSup_le fun l => ?_
    obtain ⟨L, hlen, -⟩ := exists_ltSeries_comap_eq_last hinj l
    rw [← hlen]
    exact Order.LTSeries.length_le_krullDim L
  · change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum R)
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
    intro q1 q2 hlt
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    obtain ⟨y, hy2, hy1⟩ :=
      IsConcreteLE.exists_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt)
    exact Ideal.under_lt_under_of_integral_mem_sdiff
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt.le) ⟨hy2, hy1⟩
      (Algebra.IsIntegral.isIntegral y)

theorem ringKrullDim_mvPolynomial_fin (k : Type u) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    ENat.card_eq_coe_fintype_card, Fintype.card_fin, WithBot.coe_natCast]

theorem isTranscendenceBasis_of_injective_of_isIntegral (k : Type u) (A : Type v) [Field k]
    [CommRing A] [IsDomain A] [Algebra k A] (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinj : Function.Injective g) (hint : g.IsIntegral) :
    IsTranscendenceBasis k (fun i : Fin s => g (MvPolynomial.X i)) := by
  have hind : AlgebraicIndependent k (fun i : Fin s => g (MvPolynomial.X i)) := by
    have hae : MvPolynomial.aeval (fun i : Fin s => g (MvPolynomial.X i)) = g := by
      ext i
      exact MvPolynomial.aeval_X _ i
    change Function.Injective (MvPolynomial.aeval (fun i : Fin s => g (MvPolynomial.X i)))
    rw [hae]
    exact hinj
  refine hind.isTranscendenceBasis_iff_isAlgebraic.mpr ?_
  have hrange : Algebra.adjoin k (Set.range fun i : Fin s => g (MvPolynomial.X i)) = g.range := by
    have : (Set.range fun i : Fin s => g (MvPolynomial.X i)) =
        g '' Set.range (MvPolynomial.X : Fin s → MvPolynomial (Fin s) k) := by
      ext a
      simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
    rw [this, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top]
  rw [hrange]
  have : Algebra.IsIntegral g.range A := by
    constructor
    intro a
    obtain ⟨p, hp, hpa⟩ := hint a
    refine ⟨p.map (g.rangeRestrict : MvPolynomial (Fin s) k →+* g.range), hp.map _, ?_⟩
    have h1 : (algebraMap g.range A).comp (g.rangeRestrict : MvPolynomial (Fin s) k →+* g.range) =
        (g : MvPolynomial (Fin s) k →+* A) := by
      ext x <;> rfl
    rw [Polynomial.eval₂_map, h1]
    exact hpa
  exact Algebra.IsIntegral.isAlgebraic

theorem main (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] :
    ringKrullDim A = (Cardinal.toENat (Algebra.trdeg k A) : WithBot ℕ∞) := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  have hdim : ringKrullDim A = s := by
    let : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
    have : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨fun a => hint a⟩
    have h := ringKrullDim_eq_of_isIntegral_of_injective (R := MvPolynomial (Fin s) k) (S := A)
      (by exact hinj)
    rw [← h, ringKrullDim_mvPolynomial_fin]
  have htr : Algebra.trdeg k A = s := by
    have hB := isTranscendenceBasis_of_injective_of_isIntegral k A s g hinj hint
    have h1 := hB.lift_cardinalMk_eq_trdeg
    rw [Cardinal.mk_fin, Cardinal.lift_natCast] at h1
    have h2 : Cardinal.lift.{0} (Algebra.trdeg k A) = Cardinal.lift.{0} (s : Cardinal.{v}) := by
      rw [Cardinal.lift_natCast]; exact h1.symm
    exact Cardinal.lift_injective h2
  rw [hdim, htr, Cardinal.toENat_nat]
  rfl

end RingKrullDimEqTrdeg
end Algebra

theorem _root_.Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] :
    ringKrullDim A = (Cardinal.toENat (Algebra.trdeg k A) : WithBot ℕ∞) :=
  Algebra.RingKrullDimEqTrdeg.main k A

end FiniteTypeDimension
end NOSProofs
end AbelianVarieties
end
