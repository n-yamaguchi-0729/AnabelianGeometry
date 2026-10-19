/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsRegularRing_uniqueFactorizationMonoid_of_isLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Module.StablyFree.FreeOfInvertible
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Flat.Equalizer
import Nyll.SchemeTheory.RingTheory.Localization.LocalAlgebra
import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain
import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalFiniteFreeResolution
import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalQuotientSpanSingleton
import Nyll.SchemeTheory.RingTheory.UniqueFactorizationMonoid
import Nyll.SchemeTheory.RingTheory.LinearAlgebra.InvertibleModules

/-!
# Is Regular Ring unique Factorization Monoid of is Local Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsRegularRing_uniqueFactorizationMonoid_of_isLocalRing

open IsLocalRing RingTheory.Sequence
open scoped TensorProduct

universe u v w

namespace P2mAB.StablyFree

open _root_.SchemeTheory.RegularLocalResolution.P2mAB.StablyFree

variable {R : Type u} [CommRing R]

section stablyFree

variable (S : Type v) [CommRing S] [Algebra R S]

variable {S} in
lemma step [Module.Flat R S] {K : Type w} [AddCommGroup K] [Module R K] {k : ℕ}
    (f : (Fin k → R) →ₗ[R] K) (hf : Function.Surjective f)
    [Module.Projective S (S ⊗[R] K)] :
    Module.Projective S (S ⊗[R] (LinearMap.ker f)) ∧
      (Module.IsStablyFree S (S ⊗[R] (LinearMap.ker f)) → Module.IsStablyFree S (S ⊗[R] K)) := by
  let e : S ⊗[R] (LinearMap.ker f) ≃ₗ[S] LinearMap.ker (f.baseChange S) :=
    LinearMap.tensorKerEquiv S S f
  let ι : S ⊗[R] (LinearMap.ker f) →ₗ[S] S ⊗[R] (Fin k → R) :=
    (LinearMap.ker (f.baseChange S)).subtype ∘ₗ e.toLinearMap
  let π : S ⊗[R] (Fin k → R) →ₗ[S] S ⊗[R] K := f.baseChange S
  have hι : Function.Injective ι := (Submodule.injective_subtype _).comp e.injective
  have hπ : Function.Surjective π := by
    simpa only [π, LinearMap.baseChange_eq_ltensor] using LinearMap.lTensor_surjective S hf
  have hιπ : Function.Exact ι π := by
    have h0 : Function.Exact (LinearMap.ker π).subtype π := LinearMap.exact_subtype_ker_map π
    intro y
    rw [h0 y]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨e.symm z, congrArg (LinearMap.ker π).subtype (e.apply_symm_apply z)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e x, rfl⟩
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π (LinearMap.id) hπ
  obtain ⟨E, -, -⟩ := (hιπ.splitSurjectiveEquiv hι) ⟨σ, hσ⟩
  have hproj : Module.Projective S (S ⊗[R] (LinearMap.ker f)) := by
    refine Module.Projective.of_split (E.symm.toLinearMap ∘ₗ LinearMap.inl S _ _)
      (LinearMap.fst S _ _ ∘ₗ E.toLinearMap) ?_
    apply LinearMap.ext
    intro x
    exact congrArg Prod.fst (E.apply_symm_apply (x, 0))
  refine ⟨hproj, fun hsf => ?_⟩
  obtain ⟨N, _, _, _, _, hfree⟩ := Module.IsStablyFree.exist_free_prod S (S ⊗[R] (LinearMap.ker f))
  have : Module.Finite S (S ⊗[R] (LinearMap.ker f)) :=
    Module.Finite.of_surjective
      (LinearMap.fst S (S ⊗[R] (LinearMap.ker f)) (S ⊗[R] K) ∘ₗ E.toLinearMap)
      (fun x => ⟨E.symm (x, 0), congrArg Prod.fst (E.apply_symm_apply (x, 0))⟩)
  let E' : ((S ⊗[R] K) × ((S ⊗[R] (LinearMap.ker f)) × N)) ≃ₗ[S]
      ((S ⊗[R] (Fin k → R)) × N) :=
    (LinearEquiv.prodAssoc S (S ⊗[R] K) (S ⊗[R] (LinearMap.ker f)) N).symm ≪≫ₗ
      ((LinearEquiv.prodComm S (S ⊗[R] K) (S ⊗[R] (LinearMap.ker f))).prodCongr
        (LinearEquiv.refl S N)) ≪≫ₗ
      (E.symm.prodCongr (LinearEquiv.refl S N))
  have : Module.Free S ((S ⊗[R] K) × ((S ⊗[R] (LinearMap.ker f)) × N)) := Module.Free.of_equiv
    E'.symm
  exact Module.IsStablyFree.of_free_prod S (S ⊗[R] K) ((S ⊗[R] (LinearMap.ker f)) × N)

theorem isStablyFree_of_hasFFR [Module.Flat R S] :
    ∀ (n : ℕ) (K : Type u) [AddCommGroup K] [Module R K] [Module.Projective S (S ⊗[R] K)],
      HasFFR R n K → Module.IsStablyFree S (S ⊗[R] K) := by
  intro n
  induction n with
  | zero =>
    intro K _ _ _ hK
    rw [hasFFR_zero_iff] at hK
    obtain ⟨_, _⟩ := hK
    infer_instance
  | succ n ih =>
    intro K _ _ _ hK
    rw [hasFFR_succ_iff] at hK
    obtain ⟨k, f, hf, hK'⟩ := hK
    obtain ⟨hproj, hstep⟩ := step (S := S) f hf
    exact hstep (ih _ hK')

end stablyFree

theorem isStablyFree_baseChange (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (S : Type v) [CommRing S] [Algebra R S] [Module.Flat R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective S (S ⊗[R] M)] :
    Module.IsStablyFree S (S ⊗[R] M) := by
  let d : ℕ := (maximalIdeal R).spanFinrank
  have hdim : ringKrullDim R = d := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
  obtain ⟨hproj, hstep⟩ := step (S := S) f hf
  refine hstep (isStablyFree_of_hasFFR S d _ ?_)
  exact hasFFR d hdim _

end P2mAB.StablyFree

namespace P2mAB

section idealLoc

variable {A : Type*} [CommRing A] (M : Submonoid A) (B : Type*) [CommRing B] [Algebra A B]
  [IsLocalization M B]

/-- The equivalence between tensoring an ideal to a localization and extending the ideal there. -/
noncomputable def tensorIdealEquivMap (I : Ideal A) :
    B ⊗[A] I ≃ₗ[B] (I.map (algebraMap A B) : Ideal B) :=
  have hbc : IsBaseChange B (I.toLocalized' B M (Algebra.linearMap A B)) :=
    IsLocalizedModule.isBaseChange M B _
  hbc.equiv ≪≫ₗ LinearEquiv.ofEq _ _ (Ideal.localized'_eq_map B M I)

end idealLoc

section principal

variable {S : Type*} [CommRing S]

lemma isPrincipal_of_linearEquiv (P : Ideal S) (e : P ≃ₗ[S] S) : P.IsPrincipal := by
  refine ⟨⟨(e.symm 1 : S), le_antisymm ?_ ?_⟩⟩
  · intro p hp
    have : (⟨p, hp⟩ : P) = e ⟨p, hp⟩ • e.symm 1 := by
      rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
    have h2 : p = e ⟨p, hp⟩ * (e.symm 1 : S) := by
      exact congrArg Subtype.val this
    rw [h2]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_le (α := S) (I := P) (s := {(e.symm 1 : S)}), Set.singleton_subset_iff]
    exact (e.symm 1).2

end principal

theorem ufd_of_heightOne_principal (S : Type*) [CommRing S] [IsDomain S] [IsNoetherianRing S]
    (h : ∀ P : Ideal S, P.IsPrime → P ≠ ⊥ → P.height ≤ 1 → P.IsPrincipal) :
    UniqueFactorizationMonoid S := by
  refine (UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime).mpr fun I hI hIp => ?_
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨P, hPmin, hPI⟩ := Ideal.exists_minimalPrimes_le (Ideal.span_le.mpr
    (Set.singleton_subset_iff.mpr haI) : Ideal.span {a} ≤ I)
  have hPp : P.IsPrime := hPmin.1.1
  have haP : a ∈ P := hPmin.1.2 (Ideal.subset_span rfl)
  have hP0 : P ≠ ⊥ := fun h0 => ha0 (by simpa only [h0, Submodule.mem_bot] using haP)
  have hPh : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hPmin
  obtain ⟨π, hπ⟩ := (h P hPp hP0 hPh).principal
  have hπP : P = Ideal.span {π} := hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hP0 (hπP.trans (Submodule.span_singleton_eq_bot.mpr rfl))
  refine ⟨π, hPI (hπP ▸ Ideal.subset_span rfl), ?_⟩
  exact (Ideal.span_singleton_prime hπ0).mp (hπP ▸ hPp)

section locallyPrincipal

variable {S : Type u} [CommRing S] [IsDomain S] (P : Ideal S) (hP0 : P ≠ ⊥)
  (hloc : ∀ (Q : Ideal S) [Q.IsPrime], (P.map (algebraMap S (Localization.AtPrime Q))).IsPrincipal)

include hP0 hloc

lemma nonempty_linearEquiv_localization (Q : Ideal S) [Q.IsPrime] :
    Nonempty ((P.map (algebraMap S (Localization.AtPrime Q)) : Ideal (Localization.AtPrime Q))
      ≃ₗ[Localization.AtPrime Q] Localization.AtPrime Q) := by
  obtain ⟨π, hπ⟩ := (hloc Q).principal
  have hinj : Function.Injective (algebraMap S (Localization.AtPrime Q)) :=
    IsLocalization.injective _ Q.primeCompl_le_nonZeroDivisors
  have hπ0 : π ≠ 0 := by
    rintro rfl
    obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    have : algebraMap S (Localization.AtPrime Q) a ∈ P.map (algebraMap S _) := Ideal.mem_map_of_mem
      _ haP
    rw [hπ, Submodule.span_singleton_eq_bot.mpr rfl] at this
    exact ha0 (hinj (by simpa only [Submodule.mem_bot, map_zero] using this))
  rw [show P.map (algebraMap S (Localization.AtPrime Q)) = Ideal.span {π} from hπ]
  exact ⟨(LinearEquiv.toSpanNonzeroSingleton _ _ π hπ0).symm⟩

lemma projective [IsNoetherianRing S] : Module.Projective S P := by
  have : Module.FinitePresentation S P := Module.finitePresentation_of_finite S P
  refine Module.projective_of_localization_maximal fun Q hQ => ?_
  have := hQ
  obtain ⟨e⟩ := nonempty_linearEquiv_localization P hP0 hloc Q
  let Sq := Localization.AtPrime Q
  have eL : Sq ⊗[S] P ≃ₗ[Sq] LocalizedModule Q.primeCompl P :=
    (IsLocalizedModule.isBaseChange Q.primeCompl Sq (LocalizedModule.mkLinearMap Q.primeCompl
      P)).equiv
  exact Module.Projective.of_equiv (eL.symm ≪≫ₗ tensorIdealEquivMap Q.primeCompl Sq P ≪≫ₗ e).symm

lemma invertible [IsNoetherianRing S] : Module.Invertible S P := by
  have := projective P hP0 hloc
  refine Module.Invertible.of_projective_of_forall_finrank_eq_one P fun K _ _ => ?_
  let q : Ideal S := RingHom.ker (algebraMap S K)
  have : q.IsPrime := RingHom.ker_isPrime _
  let Sq := Localization.AtPrime q
  have hunit : ∀ y : q.primeCompl, IsUnit (algebraMap S K y) := by
    intro y
    have : algebraMap S K y ≠ 0 := fun h => y.2 (RingHom.mem_ker.mpr h)
    exact isUnit_iff_ne_zero.mpr this
  let : Algebra Sq K := (IsLocalization.lift (M := q.primeCompl) hunit).toAlgebra
  have : IsScalarTower S Sq K := IsScalarTower.of_algebraMap_eq fun s => by
    simp only [RingHom.algebraMap_toAlgebra, IsLocalization.lift_eq]
  obtain ⟨e⟩ := nonempty_linearEquiv_localization P hP0 hloc q
  let e₁ : Sq ⊗[S] P ≃ₗ[Sq] Sq := tensorIdealEquivMap q.primeCompl Sq P ≪≫ₗ e
  let e₂ : K ⊗[S] P ≃ₗ[K] K :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S Sq K K P).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) e₁ ≪≫ₗ
      TensorProduct.AlgebraTensorModule.rid Sq K K
  rw [e₂.finrank_eq, Module.finrank_self]

lemma isPrincipal_of_isStablyFree [IsNoetherianRing S] [Module.IsStablyFree S P] : P.IsPrincipal :=
  by
  have := invertible P hP0 hloc
  have := Module.free_of_isStablyFree_of_invertible S P
  obtain ⟨e⟩ := (Module.Invertible.free_iff_linearEquiv (R := S) (M := P)).mp inferInstance
  exact isPrincipal_of_linearEquiv P e

end locallyPrincipal

section regular

variable {R : Type u} [CommRing R]

lemma isRegularRing_localization [IsRegularRing R] (M : Submonoid R) :
    IsRegularRing (Localization M) := by
  have : IsNoetherianRing (Localization M) := IsLocalization.isNoetherianRing M _ inferInstance
  refine (isRegularRing_iff).mpr fun p hp => ?_
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M p).toRingEquiv

end regular

section induction

lemma exists_prime_mem_maximalIdeal (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (h : maximalIdeal R ≠ ⊥) : ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ Prime x := by
  have hlt : maximalIdeal R ^ 2 < maximalIdeal R := by
    refine lt_of_le_of_ne (Ideal.pow_le_self two_ne_zero) fun heq => h ?_
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
      (IsNoetherian.noetherian _) (le_of_eq ?_) (IsLocalRing.maximalIdeal_le_jacobson _)
    rw [Ideal.smul_eq_mul, ← pow_two, heq]
  obtain ⟨x, hxm, hx2⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, hxm, hx2, ?_⟩
  have hx0 : x ≠ 0 := by rintro rfl; exact hx2 (zero_mem _)
  have hxu : ¬ IsUnit x := (IsLocalRing.mem_maximalIdeal x).mp hxm
  have : Nontrivial (R ⧸ Ideal.span {x}) :=
    Ideal.Quotient.nontrivial_iff.mpr (fun h => hxu (Ideal.span_singleton_eq_top.mp h))
  have : IsLocalRing (R ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hmin : ∀ p ∈ minimalPrimes R, x ∉ p := by
    intro p hp
    rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at hp
    subst hp
    simpa only [Submodule.mem_bot] using hx0
  have hreg :=
    (IsRegularLocalRing.quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
    R hxm hx2 hmin).1
  have := IsRegularLocalRing.isDomain (R ⧸ Ideal.span {x})
  have : (Ideal.span {x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  exact (Ideal.span_singleton_prime hx0).mp this

theorem ufd_of_ringKrullDim_le (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsRegularRing R],
      ringKrullDim R ≤ d → UniqueFactorizationMonoid R := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro R _ _ _ hd
  have : IsRegularLocalRing R := IsRegularLocalRing.of_isRegularRing_of_isLocalRing R
  have : IsDomain R := IsRegularLocalRing.isDomain R
  by_cases hm : maximalIdeal R = ⊥
  · refine UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr fun I hI hIp => ?_
    exact absurd (le_bot_iff.mp (hm ▸ IsLocalRing.le_maximalIdeal hIp.ne_top)) hI
  obtain ⟨x, hxm, -, hx⟩ := exists_prime_mem_maximalIdeal R hm
  have hx0 : x ≠ 0 := hx.ne_zero
  let S := Localization.Away x
  have : IsDomain S :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing (Submonoid.powers x) S inferInstance
  have : Module.Flat R S := IsLocalization.flat S (Submonoid.powers x)
  suffices UniqueFactorizationMonoid S from
    UniqueFactorizationMonoid.of_isLocalization_away_of_prime hx S
  have hdimR : ((maximalIdeal R).height : WithBot ℕ∞) ≤ d := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim]; exact hd
  have hdimR' : (maximalIdeal R).height ≤ d := by exact_mod_cast hdimR
  have hSQ : ∀ (Q : Ideal S) [Q.IsPrime], UniqueFactorizationMonoid (Localization.AtPrime Q) := by
    intro Q hQ
    let q : Ideal R := Q.comap (algebraMap R S)
    have hq : q.IsPrime := Ideal.comap_isPrime _ Q
    have hxq : x ∉ q := fun hxq =>
      hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hxq (IsLocalization.Away.algebraMap_isUnit x))
    have hqm : q < maximalIdeal R :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hq.ne_top) fun h => hxq (h ▸ hxm)
    have hlt : q.height < (maximalIdeal R).height :=
      Ideal.height_strict_mono_of_isPrime_of_isPrime hqm
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top_of_isPrime (I := q))
    have hnd : n < d := by
      have : (n : ℕ∞) < d := by rw [hn]; exact lt_of_lt_of_le hlt hdimR'
      exact_mod_cast this
    have : IsRegularRing (Localization.AtPrime q) := isRegularRing_localization q.primeCompl
    have hdimq : ringKrullDim (Localization.AtPrime q) ≤ n := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q), ← hn]
      rfl
    have hufd := ih n hnd (Localization.AtPrime q) hdimq
    exact MulEquiv.uniqueFactorizationMonoid
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (Submonoid.powers x)
        Q).toMulEquiv
      hufd
  refine ufd_of_heightOne_principal S fun P hPp hP0 hPh => ?_
  have hloc : ∀ (Q : Ideal S) [Q.IsPrime],
      (P.map (algebraMap S (Localization.AtPrime Q))).IsPrincipal := by
    intro Q hQ
    by_cases hPQ : P ≤ Q
    · have := hSQ Q
      have hdisj : Disjoint (Q.primeCompl : Set S) (P : Set S) := by
        rw [Set.disjoint_left]
        intro s hs hsP
        exact hs (hPQ hsP)
      have hP' : (P.map (algebraMap S (Localization.AtPrime Q))).IsPrime :=
        IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl _ P hPp hdisj
      have hinj : Function.Injective (algebraMap S (Localization.AtPrime Q)) :=
        IsLocalization.injective _ Q.primeCompl_le_nonZeroDivisors
      have hP'0 : P.map (algebraMap S (Localization.AtPrime Q)) ≠ ⊥ := by
        obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
        intro h0
        have : algebraMap S (Localization.AtPrime Q) a ∈ P.map (algebraMap S _) :=
          Ideal.mem_map_of_mem _ haP
        rw [h0, Ideal.mem_bot] at this
        exact ha0 (hinj (by simpa only [Submodule.mem_bot, map_zero] using this))
      obtain ⟨π, hπP, hπ⟩ := hP'.exists_mem_prime_of_ne_bot hP'0
      have hle : Ideal.span {π} ≤ P.map (algebraMap S (Localization.AtPrime Q)) :=
        (Ideal.span_singleton_le_iff_mem _).mpr hπP
      have : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
      have hh : (P.map (algebraMap S (Localization.AtPrime Q))).height ≤ (Ideal.span {π}).height :=
        by
        rw [IsLocalization.height_map_of_disjoint Q.primeCompl P hdisj]
        refine hPh.trans ?_
        exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
          (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero)
      have heq := Ideal.eq_of_le_of_height_le (I := Ideal.span {π}) hle hh
      exact ⟨⟨π, heq.symm⟩⟩
    · obtain ⟨s, hsP, hsQ⟩ := Set.not_subset.mp hPQ
      have htop : P.map (algebraMap S (Localization.AtPrime Q)) = ⊤ :=
        Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hsP)
          (IsLocalization.map_units (M := Q.primeCompl) _ ⟨s, hsQ⟩)
      rw [htop]
      exact ⟨⟨1, Ideal.span_singleton_one.symm⟩⟩
  let 𝔭 : Ideal R := P.comap (algebraMap R S)
  have hmap : 𝔭.map (algebraMap R S) = P := IsLocalization.map_under (Submonoid.powers x) S P
  have := projective P hP0 hloc
  let eP : S ⊗[R] 𝔭 ≃ₗ[S] P :=
    tensorIdealEquivMap (Submonoid.powers x) S 𝔭 ≪≫ₗ LinearEquiv.ofEq _ _ (by rw [hmap])
  have : Module.Projective S (S ⊗[R] 𝔭) := Module.Projective.of_equiv eP.symm
  have : Module.IsStablyFree S (S ⊗[R] 𝔭) :=
    P2mAB.StablyFree.isStablyFree_baseChange R S 𝔭
  have : Module.IsStablyFree S P := Module.IsStablyFree.equiv eP
  exact isPrincipal_of_isStablyFree P hP0 hloc

end induction

end P2mAB

open P2mAB IsLocalRing in
theorem _root_.IsRegularRing.uniqueFactorizationMonoid_of_isLocalRing
    (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R] [IsRegularRing R] :
    UniqueFactorizationMonoid R := by
  have : IsRegularLocalRing R := IsRegularLocalRing.of_isRegularRing_of_isLocalRing R
  refine ufd_of_ringKrullDim_le (maximalIdeal R).spanFinrank R (le_of_eq ?_)
  exact (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
end IsRegularRing_uniqueFactorizationMonoid_of_isLocalRing
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

attribute [-instance] instTopologicallyFGOfFiniteType
