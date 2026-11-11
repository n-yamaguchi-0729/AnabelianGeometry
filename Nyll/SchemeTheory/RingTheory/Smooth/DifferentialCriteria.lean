/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.RingHom.Surjective
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Smooth.Local
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Set
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.Transcendence
public import Nyll.SchemeTheory.RingTheory.Smooth.Cotangent
public import Nyll.SchemeTheory.RingTheory.RegularLocal.Ascent
public import Nyll.SchemeTheory.RingTheory.AlgebraNeZeroAlgebraicIndependentIsIntegralPowSmul
public import Nyll.SchemeTheory.RingTheory.Smooth.AlgebraSmoothIsDomainIsIntegrallyClosed

/-!
# Differential criteria for smoothness

Cotangent ranks control specialization over a discrete valuation ring. The other criteria
control generic transcendence degree, kernels of smooth quotients, the smooth free locus,
and descent along smooth morphisms.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.SmoothSpecialization

open TensorProduct KaehlerDifferential

universe u

namespace JacobianCriterion

theorem finrank_tensor_kaehler_eq_finrank_range_add
    {R P S : Type u} [CommRing R] [CommRing P] [CommRing S]
    [Algebra R P] [Algebra P S] [Algebra R S] [IsScalarTower R P S]
    (hsurj : Function.Surjective (algebraMap P S)) [Module.Finite P Ω[P⁄R]]
    (k : Type u) [Field k] [Algebra S k] [Algebra P k] [IsScalarTower P S k] :
    Module.finrank k (k ⊗[P] Ω[P⁄R]) =
      Module.finrank k (LinearMap.range (cotangentComplexBaseChange R S P k)) +
        Module.finrank k (k ⊗[S] Ω[S⁄R]) := by
  let P' : Algebra.Extension R S := { Ring := P, σ := _, algebraMap_σ := Function.surjInv_eq hsurj }
  have hex : Function.Exact (P'.cotangentComplex.baseChange k) (P'.toKaehler.baseChange k) := by
    have h := lTensor_exact k P'.exact_cotangentComplex_toKaehler P'.toKaehler_surjective
    intro y
    have h1 : (P'.toKaehler.baseChange k) y = (P'.toKaehler.lTensor k) y :=
      congrFun (LinearMap.baseChange_eq_lTensor _) y
    rw [h1, h y, Set.mem_range, Set.mem_range]
    exact ⟨fun ⟨z, hz⟩ => ⟨z, (congrFun (LinearMap.baseChange_eq_lTensor _) z).symm.trans hz⟩,
      fun ⟨z, hz⟩ => ⟨z, (congrFun (LinearMap.baseChange_eq_lTensor _) z).trans hz⟩⟩
  have hsurj' : Function.Surjective (P'.toKaehler.baseChange k) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact LinearMap.lTensor_surjective k P'.toKaehler_surjective
  have hrn := (P'.toKaehler.baseChange k).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj', finrank_top, LinearMap.exact_iff.mp hex] at hrn
  have e0 : k ⊗[S] P'.CotangentSpace ≃ₗ[k] k ⊗[P] Ω[P⁄R] :=
    AlgebraTensorModule.cancelBaseChange P S k k Ω[P⁄R]
  rw [← e0.finrank_eq, ← hrn, add_comm]
  congr 1
  rw [P'.cotangentComplexBaseChange_eq_lTensor_cotangentComplex k, LinearMap.range_comp,
    LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq]

section LocSurj

variable {B A : Type u} [CommRing B] [CommRing A] (g : B →+* A) (hg : Function.Surjective g)
  (p : Ideal A) [p.IsPrime] (I : Ideal B) [I.IsPrime] (hI : I = Ideal.comap g p)

include hg in
theorem ker_localRingHom :
    RingHom.ker (Localization.localRingHom I p g hI) =
      (RingHom.ker g).map (algebraMap B (Localization.AtPrime I)) := by
  subst hI
  exact IsLocalization.ker_map (Localization.AtPrime p) g
    (p.map_primeCompl_comap_of_surjective g hg)

include hg in
private theorem localRingHom_surjective_of_eq :
    Function.Surjective (Localization.localRingHom I p g hI) := by
  subst I
  exact RingHom.surjective_localRingHom_of_surjective g hg p

end LocSurj

section Tower

variable {R B A : Type u} [CommRing R] [CommRing B] [CommRing A] [Algebra R B] [Algebra R A]
  (g : B →ₐ[R] A) (p : Ideal A) [p.IsPrime] (I : Ideal B) [I.IsPrime]
  (hI : I = Ideal.comap g.toRingHom p)

theorem localRingHom_algebraMap (r : R) :
    Localization.localRingHom I p g.toRingHom hI (algebraMap R _ r) =
      algebraMap R (Localization.AtPrime p) r := by
  rw [IsScalarTower.algebraMap_apply R B (Localization.AtPrime I),
    Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply R A (Localization.AtPrime p)]
  exact congrArg (algebraMap A (Localization.AtPrime p)) (g.commutes r)

end Tower

theorem linearIndependent_one_tmul_of_map
    {P : Type u} [CommRing P] {k₁ k₂ : Type u} [Field k₁] [Field k₂] [Algebra P k₁] [Algebra P k₂]
    (σ : k₁ →+* k₂) (hσ : σ.comp (algebraMap P k₁) = algebraMap P k₂)
    {M : Type u} [AddCommGroup M] [Module P M] {ι : Type*} (m : ι → M)
    (h : LinearIndependent k₂ (fun i => (1 : k₂) ⊗ₜ[P] m i)) :
    LinearIndependent k₁ (fun i => (1 : k₁) ⊗ₜ[P] m i) := by
  classical
  let σₗ : k₁ →ₗ[P] k₂ :=
    { toFun := σ, map_add' := σ.map_add, map_smul' := fun p c => by
        simp only [Algebra.smul_def, map_mul, RingHom.id_apply]
        rw [← hσ]; rfl }
  let θ : k₁ ⊗[P] M →ₗ[P] k₂ ⊗[P] M := TensorProduct.map σₗ LinearMap.id
  have hθ : ∀ (c : k₁) (x : M), θ (c • ((1 : k₁) ⊗ₜ[P] x)) = σ c • ((1 : k₂) ⊗ₜ[P] x) := by
    intro c x
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one, smul_eq_mul,
      mul_one]
    rfl
  rw [linearIndependent_iff'] at h ⊢
  intro s c hc i hi
  have := congrArg θ hc
  rw [map_sum, map_zero] at this
  simp only [hθ] at this
  have := h s (fun j => σ (c j)) this i hi
  exact (map_eq_zero σ).mp this

theorem injective_of_linearIndependent_of_span
    {k V W : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (T : V →ₗ[k] W) {ι : Type*} [Fintype ι] (u : ι → V)
    (hu : ∀ v : V, ∃ c : ι → k, ∑ i, c i • u i = v)
    (hT : LinearIndependent k (fun i => T (u i))) : Function.Injective T := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  obtain ⟨c, rfl⟩ := hu v
  rw [LinearMap.mem_ker, map_sum] at hv
  simp only [map_smul] at hv
  have hc := Fintype.linearIndependent_iff.mp hT c hv
  simp only [hc, zero_smul, Finset.sum_const_zero]

theorem exists_sum_smul_one_tmul
    {P : Type u} [CommRing P] (k : Type u) [CommRing k] [Algebra P k]
    {ι : Type*} [Fintype ι] (w : ι → P) (K : Ideal P) (hK : K = Ideal.span (Set.range w))
    (v : k ⊗[P] K) :
    ∃ c : ι → k, ∑ i, c i • ((1 : k) ⊗ₜ[P] (⟨w i, hK ▸ Ideal.subset_span ⟨i, rfl⟩⟩ : K)) = v := by
  induction v using TensorProduct.inductionOn with
  | tmul c z =>
    obtain ⟨z, hz⟩ := z
    have hz' : z ∈ Submodule.span P (Set.range w) := by rw [hK] at hz; exact hz
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun P).mp hz'
    refine ⟨fun i => c * algebraMap P k (d i), ?_⟩
    have : (⟨z, hz⟩ : K) = ∑ i, d i • (⟨w i, hK ▸ Ideal.subset_span ⟨i, rfl⟩⟩ : K) := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_mk] using hd.symm
    rw [this, tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_tmul', smul_eq_mul, mul_one, ← smul_tmul, Algebra.smul_def, mul_comm]
  | add x y hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    exact ⟨c + d, by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩

section CotangentRank

variable (R P S κ : Type u) [CommRing R] [CommRing P] [CommRing S] [Field κ]
  [Algebra R P] [Algebra P S] [Algebra P κ] [Algebra S κ] [IsScalarTower P S κ]

private theorem cotangent_one_tmul (w : RingHom.ker (algebraMap P S)) :
    cotangentComplexBaseChange R S P κ ((1 : κ) ⊗ₜ[P] w) =
      (1 : κ) ⊗ₜ[P] D R P w.val := by
  rw [cotangentComplexBaseChange_tmul, one_smul, kerToTensor_apply]

private theorem cotangent_range_eq_span
    {ι : Type*} [Finite ι] (w : ι → P)
    (hker : RingHom.ker (algebraMap P S) = Ideal.span (Set.range w)) :
    LinearMap.range (cotangentComplexBaseChange R S P κ) =
      Submodule.span κ (Set.range (fun i => cotangentComplexBaseChange R S P κ
        ((1 : κ) ⊗ₜ[P] ⟨w i, hker ▸ Ideal.subset_span ⟨i, rfl⟩⟩))) := by
  let : Fintype ι := Fintype.ofFinite ι
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨c, rfl⟩ := exists_sum_smul_one_tmul κ w _ hker x
    rw [map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨(1 : κ) ⊗ₜ[P] ⟨w j, hker ▸ Ideal.subset_span ⟨j, rfl⟩⟩, rfl⟩

private theorem cotangent_injective_and_finrank
    {ι : Type*} [Fintype ι] (w : ι → P)
    (hker : RingHom.ker (algebraMap P S) = Ideal.span (Set.range w))
    (hli : LinearIndependent κ (fun i => (1 : κ) ⊗ₜ[P] D R P (w i))) :
    Function.Injective (cotangentComplexBaseChange R S P κ) ∧
      Module.finrank κ (LinearMap.range (cotangentComplexBaseChange R S P κ)) =
        Fintype.card ι := by
  classical
  let u : ι → κ ⊗[P] RingHom.ker (algebraMap P S) :=
    fun i => (1 : κ) ⊗ₜ[P] ⟨w i, hker ▸ Ideal.subset_span ⟨i, rfl⟩⟩
  have hcomp : (fun i => cotangentComplexBaseChange R S P κ (u i)) =
      (fun i => (1 : κ) ⊗ₜ[P] D R P (w i)) := by
    funext i
    exact cotangent_one_tmul R P S κ ⟨w i, hker ▸ Ideal.subset_span ⟨i, rfl⟩⟩
  have hliImage : LinearIndependent κ
      (fun i => cotangentComplexBaseChange R S P κ (u i)) := hcomp.symm ▸ hli
  have hgen : ∀ v, ∃ c : ι → κ, ∑ i, c i • u i = v :=
    exists_sum_smul_one_tmul κ w _ hker
  have hinj : Function.Injective (cotangentComplexBaseChange R S P κ) :=
    injective_of_linearIndependent_of_span _ u hgen hliImage
  have hliSource : LinearIndependent κ u :=
    LinearIndependent.of_comp (cotangentComplexBaseChange R S P κ) hliImage
  have hspan : Submodule.span κ (Set.range u) = ⊤ := by
    rw [eq_top_iff]
    rintro v -
    obtain ⟨c, rfl⟩ := hgen v
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b : Module.Basis ι κ (κ ⊗[P] RingHom.ker (algebraMap P S)) :=
    Module.Basis.mk hliSource hspan.ge
  refine ⟨hinj, ?_⟩
  rw [LinearMap.finrank_range_of_inj hinj]
  exact Module.finrank_eq_card_basis b

end CotangentRank

theorem eq_bot_of_finrank_tensor_eq_zero
    {T : Type u} [CommRing T] [IsLocalRing T] (K : Ideal T) (hK : K.FG)
    (k : Type u) [Field k] [Algebra T k]
    [Algebra (IsLocalRing.ResidueField T) k] [IsScalarTower T (IsLocalRing.ResidueField T) k]
    (h : Module.finrank k (k ⊗[T] K) = 0) : K = ⊥ := by
  have : Module.Finite T K := Module.Finite.iff_fg.mpr hK
  have e : k ⊗[T] K ≃ₗ[k] k ⊗[IsLocalRing.ResidueField T] (IsLocalRing.ResidueField T ⊗[T] K) :=
    (AlgebraTensorModule.cancelBaseChange T (IsLocalRing.ResidueField T) k k K).symm
  have h0 : Module.finrank (IsLocalRing.ResidueField T) (IsLocalRing.ResidueField T ⊗[T] K) = 0 :=
      by
    rw [← Module.finrank_baseChange (R := k), ← e.finrank_eq, h]
  have : Subsingleton (IsLocalRing.ResidueField T ⊗[T] K) := Module.finrank_zero_iff.mp h0
  rw [IsLocalRing.subsingleton_tensorProduct] at this
  exact Submodule.eq_bot_iff _ |>.mpr fun x hx =>
    congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : K) 0)

theorem finrank_residueField_tensor_kaehler_localization
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (p : Ideal A) [p.IsPrime] :
    Module.finrank p.ResidueField
        (p.ResidueField ⊗[Localization.AtPrime p] Ω[Localization.AtPrime p⁄R]) =
      Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[A⁄R]) := by
  have : Algebra.FormallyEtale A (Localization.AtPrime p) :=
    Algebra.FormallyEtale.of_isLocalization (M := p.primeCompl)
  have eΩ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A (Localization.AtPrime p)
  exact ((eΩ.symm.baseChange (Localization.AtPrime p) p.ResidueField _ _) ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange A (Localization.AtPrime p) p.ResidueField p.ResidueField
      Ω[A⁄R])).finrank_eq

theorem isDomain_localization_of_isSmoothAt
    {R : Type u} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {C : Type u} [CommRing C] [Algebra R C] [Algebra.FinitePresentation R C]
    (P : Ideal C) [P.IsPrime] [Algebra.IsSmoothAt R P] :
    IsDomain (Localization.AtPrime P) := by
  obtain ⟨f, hf, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R P
  have hdisj : Disjoint (↑(Submonoid.powers f) : Set C) ↑P := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hf (‹P.IsPrime›.mem_of_pow_mem n hn)
  have hP' : (P.map (algebraMap C (Localization.Away f))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) _ P ‹_› hdisj
  have hcomap : (P.map (algebraMap C (Localization.Away f))).comap
      (algebraMap C (Localization.Away f)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) _ ‹_› hdisj
  have : IsDomain (Localization.AtPrime (P.map (algebraMap C (Localization.Away f)))) :=
    (Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime R (Localization.Away
        f)
      (P.map (algebraMap C (Localization.Away f))) _).1
  have hloc : IsLocalization.AtPrime (Localization.AtPrime (P.map (algebraMap C (Localization.Away
      f))))
      ((P.map (algebraMap C (Localization.Away f))).comap (algebraMap C (Localization.Away f))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers f) _ _
  have hS : ((P.map (algebraMap C (Localization.Away f))).comap
      (algebraMap C (Localization.Away f))).primeCompl = P.primeCompl := by
    ext x
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hcomap]
  change IsLocalization _ _ at hloc
  rw [hS] at hloc
  exact (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
    (Localization.AtPrime (P.map (algebraMap C (Localization.Away f))))).toMulEquiv.isDomain

section Main

variable {R B A : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing B] [Nontrivial B] [Algebra R B] [IsNoetherianRing B] [Algebra.FinitePresentation R B]
  [Algebra.FormallySmooth R B] [Module.Free B Ω[B⁄R]] [Module.Finite B Ω[B⁄R]]
  [CommRing A] [Algebra R A]

theorem isSmoothAt_of_relations (g : B →ₐ[R] A) (hg : Function.Surjective g)
    (p q : Ideal A) [p.IsPrime] [q.IsPrime] (hqp : q ≤ p) [Algebra.IsSmoothAt R q]
    {ι : Type*} [Fintype ι] (z : ι → B) (hz : ∀ i, g (z i) = 0)
    (hli : letI := ((algebraMap (Localization.AtPrime p) p.ResidueField).comp
        (Localization.localRingHom (Ideal.comap g.toRingHom p) p g.toRingHom rfl)).toAlgebra
      LinearIndependent p.ResidueField (fun i => (1 : p.ResidueField)
        ⊗ₜ[Localization.AtPrime (Ideal.comap g.toRingHom p)]
          D R (Localization.AtPrime (Ideal.comap g.toRingHom p))
            (algebraMap B (Localization.AtPrime (Ideal.comap g.toRingHom p)) (z i))))
    (hcount : Module.finrank B Ω[B⁄R] =
      Fintype.card ι + Module.finrank q.ResidueField (q.ResidueField ⊗[A] Ω[A⁄R])) :
    Algebra.IsSmoothAt R p := by
  classical
  set J₀ : Ideal B := Ideal.span (Set.range z) with hJ₀
  have hJ₀le : ∀ b ∈ J₀, g b = 0 := by
    intro b hb
    rw [← RingHom.mem_ker]
    revert b hb
    change J₀ ≤ RingHom.ker g
    rw [hJ₀, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hz i
  have : Algebra.FinitePresentation R (B ⧸ J₀) :=
    Algebra.FinitePresentation.quotient ⟨(Set.finite_range z).toFinset, by rw
        [Set.Finite.coe_toFinset, hJ₀]⟩
  set π : B ⧸ J₀ →ₐ[R] A := Ideal.Quotient.liftₐ J₀ g hJ₀le with hπdef
  have hπmk : ∀ b : B, π (Ideal.Quotient.mk J₀ b) = g b := fun b => rfl
  have hπsurj : Function.Surjective π :=
    Ideal.Quotient.lift_surjective_of_surjective J₀ hJ₀le hg
  have hπcomp : π.toRingHom.comp (Ideal.Quotient.mk J₀) = g.toRingHom := RingHom.ext fun b => rfl
  set 𝔓 : Ideal B := Ideal.comap g.toRingHom p with h𝔓
  set 𝔓C : Ideal (B ⧸ J₀) := Ideal.comap π.toRingHom p with h𝔓C
  set 𝔮C : Ideal (B ⧸ J₀) := Ideal.comap π.toRingHom q with h𝔮C
  have h𝔮𝔓 : 𝔮C ≤ 𝔓C := Ideal.comap_mono hqp
  have h𝔓' : 𝔓 = Ideal.comap (Ideal.Quotient.mk J₀) 𝔓C := by
    rw [h𝔓C, Ideal.comap_comap, hπcomp]
  set φ : Localization.AtPrime 𝔓 →+* Localization.AtPrime p :=
    Localization.localRingHom 𝔓 p g.toRingHom rfl with hφ
  set χ : Localization.AtPrime 𝔓 →+* Localization.AtPrime 𝔓C :=
    Localization.localRingHom 𝔓 𝔓C (Ideal.Quotient.mk J₀) h𝔓' with hχ
  set φ' : Localization.AtPrime 𝔓C →+* Localization.AtPrime p :=
    Localization.localRingHom 𝔓C p π.toRingHom rfl with hφ'
  set φq : Localization.AtPrime 𝔮C →+* Localization.AtPrime q :=
    Localization.localRingHom 𝔮C q π.toRingHom rfl with hφq
  have hφsurj : Function.Surjective φ := RingHom.surjective_localRingHom_of_surjective g.toRingHom
      hg p
  have hχsurj : Function.Surjective χ :=
    localRingHom_surjective_of_eq (Ideal.Quotient.mk J₀)
      Ideal.Quotient.mk_surjective 𝔓C 𝔓 h𝔓'
  have hφ'surj : Function.Surjective φ' := RingHom.surjective_localRingHom_of_surjective
      π.toRingHom hπsurj p
  have hφqsurj : Function.Surjective φq := RingHom.surjective_localRingHom_of_surjective
      π.toRingHom hπsurj q
  have hχker : RingHom.ker χ = J₀.map (algebraMap B (Localization.AtPrime 𝔓)) := by
    rw [hχ, ker_localRingHom (Ideal.Quotient.mk J₀) Ideal.Quotient.mk_surjective 𝔓C 𝔓 h𝔓',
      Ideal.mk_ker]
  have hφ'ker : RingHom.ker φ' = (RingHom.ker π).map (algebraMap (B ⧸ J₀) (Localization.AtPrime
      𝔓C)) :=
    ker_localRingHom π.toRingHom hπsurj p 𝔓C rfl
  have hφqker : RingHom.ker φq = (RingHom.ker π).map (algebraMap (B ⧸ J₀) (Localization.AtPrime
      𝔮C)) :=
    ker_localRingHom π.toRingHom hπsurj q 𝔮C rfl
  have hφ'χ : φ'.comp χ = φ := by
    refine IsLocalization.ringHom_ext 𝔓.primeCompl (RingHom.ext fun b => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [hχ, Localization.localRingHom_to_map, hφ', Localization.localRingHom_to_map, hφ,
      Localization.localRingHom_to_map]
    rfl
  let iPS : Algebra (Localization.AtPrime 𝔓) (Localization.AtPrime p) := φ.toAlgebra
  let iPS' : Algebra (Localization.AtPrime 𝔓) (Localization.AtPrime 𝔓C) := χ.toAlgebra
  let iS'S : Algebra (Localization.AtPrime 𝔓C) (Localization.AtPrime p) := φ'.toAlgebra
  let iTU : Algebra (Localization.AtPrime 𝔮C) (Localization.AtPrime q) := φq.toAlgebra
  have : IsScalarTower R (Localization.AtPrime 𝔓) (Localization.AtPrime p) :=
    IsScalarTower.of_algebraMap_eq fun r => (localRingHom_algebraMap g p 𝔓 rfl r).symm
  have : IsScalarTower R (Localization.AtPrime 𝔓C) (Localization.AtPrime p) :=
    IsScalarTower.of_algebraMap_eq fun r => (localRingHom_algebraMap π p 𝔓C rfl r).symm
  have : IsScalarTower R (Localization.AtPrime 𝔮C) (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq fun r => (localRingHom_algebraMap π q 𝔮C rfl r).symm
  have : IsScalarTower R (Localization.AtPrime 𝔓) (Localization.AtPrime 𝔓C) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change _ = χ _
      rw [hχ, IsScalarTower.algebraMap_apply R B (Localization.AtPrime 𝔓),
        Localization.localRingHom_to_map,
        IsScalarTower.algebraMap_apply R (B ⧸ J₀) (Localization.AtPrime 𝔓C)]
      rfl
  have : IsScalarTower (Localization.AtPrime 𝔓) (Localization.AtPrime 𝔓C) (Localization.AtPrime p)
      :=
    IsScalarTower.of_algebraMap_eq fun x => (RingHom.congr_fun hφ'χ x).symm
  let iPκ : Algebra (Localization.AtPrime 𝔓) p.ResidueField :=
    ((algebraMap (Localization.AtPrime p) p.ResidueField).comp φ).toAlgebra
  have : IsScalarTower (Localization.AtPrime 𝔓) (Localization.AtPrime p) p.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let iPκ' : Algebra (Localization.AtPrime 𝔓) 𝔓C.ResidueField :=
    ((algebraMap (Localization.AtPrime 𝔓C) 𝔓C.ResidueField).comp χ).toAlgebra
  have : IsScalarTower (Localization.AtPrime 𝔓) (Localization.AtPrime 𝔓C) 𝔓C.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let iTκU : Algebra (Localization.AtPrime 𝔮C) q.ResidueField :=
    ((algebraMap (Localization.AtPrime q) q.ResidueField).comp φq).toAlgebra
  have : IsScalarTower (Localization.AtPrime 𝔮C) (Localization.AtPrime q) q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : SMulCommClass (Localization.AtPrime 𝔓) p.ResidueField p.ResidueField :=
    @Algebra.to_smulCommClass _ _ _ _ iPκ
  have hcommPκ : SMulCommClass (Localization.AtPrime 𝔓) 𝔓C.ResidueField 𝔓C.ResidueField :=
    @Algebra.to_smulCommClass _ _ _ _ iPκ'
  have hcommTκ : SMulCommClass (Localization.AtPrime 𝔮C) q.ResidueField q.ResidueField :=
    @Algebra.to_smulCommClass _ _ _ _ iTκU
  let tensorDifferentials : Module 𝔓C.ResidueField
      (𝔓C.ResidueField ⊗[Localization.AtPrime 𝔓] Ω[Localization.AtPrime 𝔓⁄R]) :=
    @TensorProduct.leftModule (Localization.AtPrime 𝔓) 𝔓C.ResidueField _ _
      𝔓C.ResidueField Ω[Localization.AtPrime 𝔓⁄R] _ _ _
      (@Algebra.toModule _ _ _ _ iPκ') _ hcommPκ
  let tensorKernelQ : Module q.ResidueField
      (q.ResidueField ⊗[Localization.AtPrime 𝔮C]
        RingHom.ker (algebraMap (Localization.AtPrime 𝔮C) (Localization.AtPrime q))) :=
    @TensorProduct.leftModule (Localization.AtPrime 𝔮C) q.ResidueField _ _
      q.ResidueField (RingHom.ker (algebraMap (Localization.AtPrime 𝔮C)
        (Localization.AtPrime q))) _ _ _ (@Algebra.toModule _ _ _ _ iTκU) _ hcommTκ
  have : Algebra.FormallyEtale B (Localization.AtPrime 𝔓) :=
    Algebra.FormallyEtale.of_isLocalization (M := 𝔓.primeCompl)
  have : Algebra.FormallySmooth R (Localization.AtPrime 𝔓) :=
    Algebra.FormallySmooth.comp R B (Localization.AtPrime 𝔓)
  have eΩP : Localization.AtPrime 𝔓 ⊗[B] Ω[B⁄R] ≃ₗ[Localization.AtPrime 𝔓]
      Ω[Localization.AtPrime 𝔓⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B (Localization.AtPrime 𝔓)
  have : Module.Free (Localization.AtPrime 𝔓) Ω[Localization.AtPrime 𝔓⁄R] := Module.Free.of_equiv
      eΩP
  have : Module.Finite (Localization.AtPrime 𝔓) Ω[Localization.AtPrime 𝔓⁄R] :=
    Module.Finite.equiv eΩP
  have hrankP : Module.finrank (Localization.AtPrime 𝔓) Ω[Localization.AtPrime 𝔓⁄R] =
      Module.finrank B Ω[B⁄R] := by
    rw [← eΩP.finrank_eq, Module.finrank_baseChange]
  have hzker : ∀ i, algebraMap B (Localization.AtPrime 𝔓) (z i) ∈ RingHom.ker χ := fun i => by
    rw [hχker]; exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
  have hkerspan : RingHom.ker (algebraMap (Localization.AtPrime 𝔓) (Localization.AtPrime 𝔓C)) =
      Ideal.span (Set.range (fun i => algebraMap B (Localization.AtPrime 𝔓) (z i))) := by
    change RingHom.ker χ = _
    rw [hχker, hJ₀, Ideal.map_span, ← Set.range_comp]
    rfl
  have hli' : LinearIndependent 𝔓C.ResidueField (fun i => (1 : 𝔓C.ResidueField)
      ⊗ₜ[Localization.AtPrime 𝔓] D R (Localization.AtPrime 𝔓)
        (algebraMap B (Localization.AtPrime 𝔓) (z i))) := by
    have : IsLocalHom φ' := Localization.isLocalHom_localRingHom 𝔓C p π.toRingHom rfl
    refine linearIndependent_one_tmul_of_map (IsLocalRing.ResidueField.map φ') ?_ _ hli
    refine RingHom.ext fun x => ?_
    change IsLocalRing.ResidueField.map φ' (IsLocalRing.residue _ (χ x)) =
      IsLocalRing.residue _ (φ x)
    rw [IsLocalRing.ResidueField.map_residue, ← hφ'χ]
    rfl
  obtain ⟨hinj', hrange'⟩ := cotangent_injective_and_finrank R
    (Localization.AtPrime 𝔓) (Localization.AtPrime 𝔓C) 𝔓C.ResidueField
    (fun i => algebraMap B (Localization.AtPrime 𝔓) (z i)) hkerspan hli'
  have hS'sm : Algebra.IsSmoothAt R 𝔓C :=
    (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField (R := R)
      (S := Localization.AtPrime 𝔓C) (Localization.AtPrime 𝔓) hχsurj
        (IsNoetherian.noetherian _)).mpr hinj'
  have : Module.Finite (Localization.AtPrime 𝔓C) Ω[Localization.AtPrime 𝔓C⁄R] := inferInstance
  have : Module.Free (Localization.AtPrime 𝔓C) Ω[Localization.AtPrime 𝔓C⁄R] :=
    Module.free_of_flat_of_isLocalRing
  have hcountS' := finrank_tensor_kaehler_eq_finrank_range_add (R := R) hχsurj 𝔓C.ResidueField
  have hrankS' : Module.finrank (Localization.AtPrime 𝔓C) Ω[Localization.AtPrime 𝔓C⁄R] =
      Module.finrank q.ResidueField (q.ResidueField ⊗[A] Ω[A⁄R]) := by
    rw [← Module.finrank_baseChange (R := 𝔓C.ResidueField)]
    rw [hrange', Module.finrank_baseChange, hrankP, hcount] at hcountS'
    omega
  have : IsDomain (Localization.AtPrime 𝔓C) := isDomain_localization_of_isSmoothAt (R := R) 𝔓C
  have hTsm : Algebra.IsSmoothAt R 𝔮C := by
    have hmem : (⟨𝔓C, inferInstance⟩ : PrimeSpectrum (B ⧸ J₀)) ∈ Algebra.smoothLocus R (B ⧸ J₀) :=
      hS'sm
    have hspec : (⟨𝔮C, inferInstance⟩ : PrimeSpectrum (B ⧸ J₀)) ⤳ ⟨𝔓C, inferInstance⟩ :=
      (PrimeSpectrum.le_iff_specializes _ _).mp h𝔮𝔓
    exact hspec.mem_open Algebra.isOpen_smoothLocus hmem
  let iS'T : Algebra (Localization.AtPrime 𝔓C) (Localization.AtPrime 𝔮C) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.AtPrime 𝔓C)
      (Localization.AtPrime 𝔮C) 𝔓C.primeCompl 𝔮C.primeCompl
      (fun x hx h => hx (h𝔮𝔓 h))
  have : IsScalarTower (B ⧸ J₀) (Localization.AtPrime 𝔓C) (Localization.AtPrime 𝔮C) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ _
  have : IsScalarTower R (Localization.AtPrime 𝔓C) (Localization.AtPrime 𝔮C) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R (B ⧸ J₀) (Localization.AtPrime 𝔮C),
        IsScalarTower.algebraMap_apply R (B ⧸ J₀) (Localization.AtPrime 𝔓C),
        ← IsScalarTower.algebraMap_apply (B ⧸ J₀)]
  have : IsLocalization (𝔮C.primeCompl.map (algebraMap (B ⧸ J₀) (Localization.AtPrime 𝔓C)))
      (Localization.AtPrime 𝔮C) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ 𝔓C.primeCompl 𝔮C.primeCompl
      (fun x hx h => hx (h𝔮𝔓 h))
  have : Algebra.FormallyEtale (Localization.AtPrime 𝔓C) (Localization.AtPrime 𝔮C) :=
    Algebra.FormallyEtale.of_isLocalization
      (M := 𝔮C.primeCompl.map (algebraMap (B ⧸ J₀) (Localization.AtPrime 𝔓C)))
  have eΩT : Localization.AtPrime 𝔮C ⊗[Localization.AtPrime 𝔓C] Ω[Localization.AtPrime 𝔓C⁄R]
      ≃ₗ[Localization.AtPrime 𝔮C] Ω[Localization.AtPrime 𝔮C⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R _ _
  have : Module.Free (Localization.AtPrime 𝔮C) Ω[Localization.AtPrime 𝔮C⁄R] :=
    Module.Free.of_equiv eΩT
  have : Module.Finite (Localization.AtPrime 𝔮C) Ω[Localization.AtPrime 𝔮C⁄R] :=
    Module.Finite.equiv eΩT
  have hrankT : Module.finrank (Localization.AtPrime 𝔮C) Ω[Localization.AtPrime 𝔮C⁄R] =
      Module.finrank q.ResidueField (q.ResidueField ⊗[A] Ω[A⁄R]) := by
    rw [← eΩT.finrank_eq, Module.finrank_baseChange, hrankS']
  have hinjU : Function.Injective (cotangentComplexBaseChange R (Localization.AtPrime q)
      (Localization.AtPrime 𝔮C) q.ResidueField) :=
    (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField (R := R)
      (S := Localization.AtPrime q) (Localization.AtPrime 𝔮C) hφqsurj
        (IsNoetherian.noetherian _)).mp ‹Algebra.IsSmoothAt R q›
  have hcountU := finrank_tensor_kaehler_eq_finrank_range_add (R := R) hφqsurj q.ResidueField
  rw [Module.finrank_baseChange, hrankT, finrank_residueField_tensor_kaehler_localization,
    LinearMap.finrank_range_of_inj hinjU] at hcountU
  have hkerU : RingHom.ker φq = ⊥ := by
    have : IsLocalHom φq := Localization.isLocalHom_localRingHom 𝔮C q π.toRingHom rfl
    let : Algebra (IsLocalRing.ResidueField (Localization.AtPrime 𝔮C)) q.ResidueField :=
      (IsLocalRing.ResidueField.map φq).toAlgebra
    have : IsScalarTower (Localization.AtPrime 𝔮C)
        (IsLocalRing.ResidueField (Localization.AtPrime 𝔮C)) q.ResidueField :=
      IsScalarTower.of_algebraMap_eq fun x => by
        change IsLocalRing.residue _ (φq x) = IsLocalRing.ResidueField.map φq (IsLocalRing.residue
            _ x)
        rw [IsLocalRing.ResidueField.map_residue]
    have h0 : Module.finrank q.ResidueField (q.ResidueField ⊗[Localization.AtPrime 𝔮C]
        (RingHom.ker (algebraMap (Localization.AtPrime 𝔮C) (Localization.AtPrime q)))) = 0 := by
      have hcountU' : Module.finrank q.ResidueField (q.ResidueField ⊗[A] Ω[A⁄R]) =
          Module.finrank q.ResidueField (q.ResidueField ⊗[Localization.AtPrime 𝔮C]
            RingHom.ker (algebraMap (Localization.AtPrime 𝔮C) (Localization.AtPrime q))) +
            Module.finrank q.ResidueField (q.ResidueField ⊗[A] Ω[A⁄R]) := hcountU
      omega
    exact eq_bot_of_finrank_tensor_eq_zero _ (IsNoetherian.noetherian _) q.ResidueField h0
  have hkerS' : RingHom.ker φ' = ⊥ := by
    rw [hφ'ker, Ideal.map_eq_bot_iff_le_ker]
    intro c hc
    rw [RingHom.mem_ker]
    have hcT : algebraMap (B ⧸ J₀) (Localization.AtPrime 𝔮C) c = 0 := by
      have hmem : algebraMap (B ⧸ J₀) (Localization.AtPrime 𝔮C) c ∈ RingHom.ker φq := by
        rw [hφqker]; exact Ideal.mem_map_of_mem _ hc
      rwa [hkerU, Ideal.mem_bot] at hmem
    obtain ⟨⟨t, ht⟩, htc⟩ := (IsLocalization.map_eq_zero_iff 𝔮C.primeCompl _ c).mp hcT
    have hmul : algebraMap (B ⧸ J₀) (Localization.AtPrime 𝔓C) t *
        algebraMap (B ⧸ J₀) (Localization.AtPrime 𝔓C) c = 0 := by
      rw [← map_mul, htc, map_zero]
    rcases mul_eq_zero.mp hmul with h0 | h0
    · exfalso
      obtain ⟨⟨s, hs⟩, hst⟩ := (IsLocalization.map_eq_zero_iff 𝔓C.primeCompl _ t).mp h0
      have : s * t ∈ 𝔮C := by rw [hst]; exact 𝔮C.zero_mem
      rcases (inferInstance : 𝔮C.IsPrime).mem_or_mem this with h1 | h1
      · exact hs (h𝔮𝔓 h1)
      · exact ht h1
    · exact h0
  have hφ'inj : Function.Injective φ' := (RingHom.injective_iff_ker_eq_bot φ').mpr hkerS'
  let φ'ₐ : Localization.AtPrime 𝔓C →ₐ[R] Localization.AtPrime p :=
    { φ' with commutes' := fun r => localRingHom_algebraMap π p 𝔓C rfl r }
  exact Algebra.FormallySmooth.of_equiv (AlgEquiv.ofBijective φ'ₐ ⟨hφ'inj, hφ'surj⟩)

end Main

end JacobianCriterion

open JacobianCriterion

theorem _root_.Algebra.isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (p q : Ideal A) [p.IsPrime] [q.IsPrime] (hqp : q ≤ p) [Algebra.IsSmoothAt R q]
    (h : Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[A⁄R]) =
      Module.finrank q.ResidueField (q.ResidueField ⊗[A] Ω[A⁄R])) :
    Algebra.IsSmoothAt R p := by
  classical
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType R A›
  set 𝔓 : Ideal (MvPolynomial (Fin n) R) := Ideal.comap g.toRingHom p with h𝔓
  set φ : Localization.AtPrime 𝔓 →+* Localization.AtPrime p :=
    Localization.localRingHom 𝔓 p g.toRingHom rfl with hφ
  have hφsurj : Function.Surjective φ := RingHom.surjective_localRingHom_of_surjective g.toRingHom
      hg p
  let iPS : Algebra (Localization.AtPrime 𝔓) (Localization.AtPrime p) := φ.toAlgebra
  have : IsScalarTower R (Localization.AtPrime 𝔓) (Localization.AtPrime p) :=
    IsScalarTower.of_algebraMap_eq fun r => (localRingHom_algebraMap g p 𝔓 rfl r).symm
  let iPκ : Algebra (Localization.AtPrime 𝔓) p.ResidueField :=
    ((algebraMap (Localization.AtPrime p) p.ResidueField).comp
      (Localization.localRingHom (Ideal.comap g.toRingHom p) p g.toRingHom rfl)).toAlgebra
  have : IsScalarTower (Localization.AtPrime 𝔓) (Localization.AtPrime p) p.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcommPκ : SMulCommClass (Localization.AtPrime 𝔓) p.ResidueField p.ResidueField :=
    @Algebra.to_smulCommClass _ _ _ _ iPκ
  let tensorDifferentials : Module p.ResidueField
      (p.ResidueField ⊗[Localization.AtPrime 𝔓] Ω[Localization.AtPrime 𝔓⁄R]) :=
    @TensorProduct.leftModule (Localization.AtPrime 𝔓) p.ResidueField _ _
      p.ResidueField Ω[Localization.AtPrime 𝔓⁄R] _ _ _
      (@Algebra.toModule _ _ _ _ iPκ) _ hcommPκ
  have : Algebra.FormallyEtale (MvPolynomial (Fin n) R) (Localization.AtPrime 𝔓) :=
    Algebra.FormallyEtale.of_isLocalization (M := 𝔓.primeCompl)
  have eΩP : Localization.AtPrime 𝔓 ⊗[MvPolynomial (Fin n) R] Ω[MvPolynomial (Fin n) R⁄R]
      ≃ₗ[Localization.AtPrime 𝔓] Ω[Localization.AtPrime 𝔓⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial (Fin n) R) _
  have : Module.Free (Localization.AtPrime 𝔓) Ω[Localization.AtPrime 𝔓⁄R] := Module.Free.of_equiv
      eΩP
  have : Module.Finite (Localization.AtPrime 𝔓) Ω[Localization.AtPrime 𝔓⁄R] :=
    Module.Finite.equiv eΩP
  have hrankP : Module.finrank (Localization.AtPrime 𝔓) Ω[Localization.AtPrime 𝔓⁄R] =
      Module.finrank (MvPolynomial (Fin n) R) Ω[MvPolynomial (Fin n) R⁄R] := by
    rw [← eΩP.finrank_eq, Module.finrank_baseChange]
  have hcount := finrank_tensor_kaehler_eq_finrank_range_add (R := R) hφsurj p.ResidueField
  rw [Module.finrank_baseChange, hrankP, finrank_residueField_tensor_kaehler_localization, h]
    at hcount
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (RingHom.ker g.toRingHom) : (RingHom.ker
      g.toRingHom).FG)
  have hkerφ : RingHom.ker (algebraMap (Localization.AtPrime 𝔓) (Localization.AtPrime p)) =
      Ideal.span (Set.range (fun j : s =>
        algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime 𝔓) (j : MvPolynomial (Fin n)
            R))) := by
    change RingHom.ker φ = _
    rw [hφ, ker_localRingHom g.toRingHom hg p 𝔓 rfl, ← hs, Ideal.map_span]
    congr 1
    ext x
    simp only [Set.mem_image, Finset.mem_coe, Set.mem_range, Subtype.exists, exists_prop]
  set u : s → p.ResidueField ⊗[Localization.AtPrime 𝔓]
      RingHom.ker (algebraMap (Localization.AtPrime 𝔓) (Localization.AtPrime p)) :=
    fun j => (1 : p.ResidueField) ⊗ₜ[Localization.AtPrime 𝔓]
      (⟨algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime 𝔓) (j : MvPolynomial (Fin n) R),
        hkerφ ▸ Ideal.subset_span ⟨j, rfl⟩⟩ :
        RingHom.ker (algebraMap (Localization.AtPrime 𝔓) (Localization.AtPrime p))) with hu
  set v : s → p.ResidueField ⊗[Localization.AtPrime 𝔓] Ω[Localization.AtPrime 𝔓⁄R] :=
    fun j => cotangentComplexBaseChange R (Localization.AtPrime p) (Localization.AtPrime 𝔓)
      p.ResidueField (u j) with hv
  have hW : LinearMap.range (cotangentComplexBaseChange R (Localization.AtPrime p)
      (Localization.AtPrime 𝔓) p.ResidueField) = Submodule.span p.ResidueField (Set.range v) := by
    exact cotangent_range_eq_span R (Localization.AtPrime 𝔓) (Localization.AtPrime p)
      p.ResidueField (fun j : s =>
        algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime 𝔓) j) hkerφ
  obtain ⟨ι, a, hainj, hspan, hli⟩ := exists_linearIndependent' (K := p.ResidueField) v
  have : Finite ι := Finite.of_injective a hainj
  let : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = Module.finrank p.ResidueField (LinearMap.range
      (cotangentComplexBaseChange R (Localization.AtPrime p) (Localization.AtPrime 𝔓)
        p.ResidueField)) := by
    calc
      Fintype.card ι = Module.finrank p.ResidueField
          (Submodule.span p.ResidueField (Set.range (v ∘ a))) :=
        (finrank_span_eq_card hli).symm
      _ = Module.finrank p.ResidueField
          (Submodule.span p.ResidueField (Set.range v)) :=
        congrArg (fun W : Submodule p.ResidueField
          (p.ResidueField ⊗[Localization.AtPrime 𝔓] Ω[Localization.AtPrime 𝔓⁄R]) =>
            Module.finrank p.ResidueField W) hspan
      _ = _ := congrArg (fun W : Submodule p.ResidueField
          (p.ResidueField ⊗[Localization.AtPrime 𝔓] Ω[Localization.AtPrime 𝔓⁄R]) =>
            Module.finrank p.ResidueField W) hW.symm
  set z : ι → MvPolynomial (Fin n) R := fun i => (a i : MvPolynomial (Fin n) R) with hzdef
  have hz : ∀ i, g (z i) = 0 := fun i => by
    have : (a i : MvPolynomial (Fin n) R) ∈ RingHom.ker g.toRingHom := by
      rw [← hs]; exact Ideal.subset_span (a i).2
    exact this
  have hli' : LinearIndependent p.ResidueField (fun i => (1 : p.ResidueField)
      ⊗ₜ[Localization.AtPrime 𝔓] D R (Localization.AtPrime 𝔓)
        (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime 𝔓) (z i))) := by
    have hvz : v ∘ a = (fun i => (1 : p.ResidueField)
        ⊗ₜ[Localization.AtPrime 𝔓] D R (Localization.AtPrime 𝔓)
          (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime 𝔓) (z i))) := by
      funext i
      exact cotangent_one_tmul R (Localization.AtPrime 𝔓) (Localization.AtPrime p)
        p.ResidueField ⟨algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime 𝔓) (z i),
          hkerφ ▸ Ideal.subset_span ⟨a i, rfl⟩⟩
    exact hvz ▸ hli
  refine isSmoothAt_of_relations g hg p q hqp z hz hli' ?_
  rw [hcard]
  exact hcount

end AbelianVarieties.NOSProofs.SmoothSpecialization
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_FiniteType_exists_notMem_under_forall_trdeg_quotient_le.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.GenericTranscendence

open Polynomial

universe u v

namespace GenericBound

open AbelianVarieties.NOSProofs.TensorTranscendence.TensorPrimes

theorem main
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (𝔮 : Ideal B) [𝔮.IsPrime] :
    ∃ s : A, s ∉ 𝔮.under A ∧ ∀ (𝔔 : Ideal B) [𝔔.IsPrime], 𝔮 ≤ 𝔔 → s ∉ 𝔔.under A →
      Algebra.trdeg (A ⧸ 𝔔.under A) (B ⧸ 𝔔) ≤ Algebra.trdeg (A ⧸ 𝔮.under A) (B ⧸ 𝔮) := by
  classical
  set 𝔭 := 𝔮.under A with h𝔭
  have : Algebra.FiniteType (A ⧸ 𝔭) (B ⧸ 𝔮) := inferInstance
  obtain ⟨r, hr, d, z, hz, hint⟩ :=
    Algebra.exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType
      (R := A ⧸ 𝔭) (C := B ⧸ 𝔮)
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hs : s ∉ 𝔭 := fun h => hr (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  refine ⟨s, hs, ?_⟩
  intro 𝔔 _ h𝔮𝔔 hs𝔔
  have hd : (d : Cardinal) ≤ Algebra.trdeg (A ⧸ 𝔭) (B ⧸ 𝔮) := by
    simpa only [Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_uzero] using
      hz.lift_cardinalMk_le_trdeg
  refine le_trans ?_ hd
  set 𝔭' := 𝔔.under A with h𝔭'
  have h𝔭𝔭' : 𝔭 ≤ 𝔭' := Ideal.comap_mono h𝔮𝔔
  let πR : A ⧸ 𝔭 →+* A ⧸ 𝔭' := Ideal.Quotient.factor h𝔭𝔭'
  let πC : B ⧸ 𝔮 →+* B ⧸ 𝔔 := Ideal.Quotient.factor h𝔮𝔔
  have hπ : ∀ x : A ⧸ 𝔭, πC (algebraMap (A ⧸ 𝔭) (B ⧸ 𝔮) x) = algebraMap (A ⧸ 𝔭') (B ⧸ 𝔔) (πR x) :=
      by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  have hr' : πR (Ideal.Quotient.mk 𝔭 s) ≠ 0 := by
    change Ideal.Quotient.mk 𝔭' s ≠ 0
    exact fun h => hs𝔔 (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let z' : Fin d → B ⧸ 𝔔 := fun i => πC (z i)
  let D : Subalgebra (A ⧸ 𝔭) (B ⧸ 𝔮) := Algebra.adjoin (A ⧸ 𝔭) (Set.range z)
  let D' : Subalgebra (A ⧸ 𝔭') (B ⧸ 𝔔) := Algebra.adjoin (A ⧸ 𝔭') (Set.range z')
  have hDD' : ∀ x ∈ D, πC x ∈ D' := by
    intro x hx
    refine Algebra.adjoin_induction (hx := hx) ?_ ?_ ?_ ?_
    · rintro _ ⟨i, rfl⟩; exact Algebra.subset_adjoin ⟨i, rfl⟩
    · intro x; rw [hπ]; exact Subalgebra.algebraMap_mem _ _
    · intro x y _ _ hx hy; rw [map_add]; exact D'.add_mem hx hy
    · intro x y _ _ hx hy; rw [map_mul]; exact D'.mul_mem hx hy
  have : Algebra.IsAlgebraic D' (B ⧸ 𝔔) := by
    refine ⟨fun c' => ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.factor_surjective h𝔮𝔔 c'
    change IsAlgebraic D' (πC c)
    obtain ⟨n, hn⟩ := hint c
    have h1 : IsIntegral D' (πC ((Ideal.Quotient.mk 𝔭 s) ^ n • c)) := isIntegral_map_of_forall_mem
        πC D D' hDD' hn
    simp only [Algebra.smul_def, map_pow, map_mul] at h1
    rw [hπ] at h1
    let ρ : D' := ⟨algebraMap (A ⧸ 𝔭') (B ⧸ 𝔔) (πR (Ideal.Quotient.mk 𝔭 s)) ^ n,
      D'.pow_mem (Subalgebra.algebraMap_mem _ _) n⟩
    have hρ : (ρ : B ⧸ 𝔔) ≠ 0 := by
      refine pow_ne_zero _ ?_
      rw [Ne, ← map_zero (algebraMap (A ⧸ 𝔭') (B ⧸ 𝔔)),
        (FaithfulSMul.algebraMap_injective (A ⧸ 𝔭') (B ⧸ 𝔔)).eq_iff]
      exact hr'
    have hρ' : ρ ≠ 0 := fun h => hρ (by rw [h]; rfl)
    have h2 : IsAlgebraic D' (ρ • πC c) := by
      rw [Algebra.smul_def]
      exact h1.isAlgebraic
    exact IsAlgebraic.of_smul (mem_nonZeroDivisors_of_ne_zero hρ') h2
  have hrange : Cardinal.mk (Set.range z') ≤ (d : Cardinal.{v}) := by
    simpa only [Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_uzero] using
      Cardinal.mk_range_le_lift (f := z')
  exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk (A ⧸ 𝔭') (Set.range z')).trans hrange

end GenericBound

theorem _root_.Algebra.FiniteType.exists_notMem_under_forall_trdeg_quotient_le
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (𝔮 : Ideal B) [𝔮.IsPrime] :
    ∃ s : A, s ∉ 𝔮.under A ∧ ∀ (𝔔 : Ideal B) [𝔔.IsPrime], 𝔮 ≤ 𝔔 → s ∉ 𝔔.under A →
      Algebra.trdeg (A ⧸ 𝔔.under A) (B ⧸ 𝔔) ≤ Algebra.trdeg (A ⧸ 𝔮.under A) (B ⧸ 𝔮) :=
  GenericBound.main 𝔮

end AbelianVarieties.NOSProofs.GenericTranscendence
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.CotangentKernel

open TensorProduct

universe u

theorem _root_.Algebra.ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le
    {k P S : Type u} [Field k] [CommRing P] [CommRing S] [IsLocalRing P] [IsLocalRing S]
        [IsNoetherianRing P]
    [Algebra k P] [Algebra k S] [Algebra P S] [IsScalarTower k P S]
    [Algebra.FormallySmooth k P] [Algebra.FormallySmooth k S] [Module.Finite P Ω[P⁄k]]
    (hPS : Function.Surjective (algebraMap P S))
    (hrank : Module.finrank (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField S ⊗[S] (S ⊗[P]
        Ω[P⁄k])) ≤
      Module.finrank (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField S ⊗[S] Ω[S⁄k])) :
    RingHom.ker (algebraMap P S) = ⊥ := by
  classical
  set ι := KaehlerDifferential.kerCotangentToTensor k P S with hι
  set g := KaehlerDifferential.mapBaseChange k P S with hg
  have hex : Function.Exact ι g := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k
      P S hPS
  have hgs : Function.Surjective g := KaehlerDifferential.mapBaseChange_surjective k P S hPS
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection hPS).mp ‹Algebra.FormallySmooth k S›
  have hlι : ∀ c, l (ι c) = c := fun c => by
    exact congrArg (fun f => f c) hl
  have hιinj : Function.Injective ι := fun a b h => by rw [← hlι a, ← hlι b, h]
  set N : Submodule S (S ⊗[P] Ω[P⁄k]) := LinearMap.ker g with hN
  have hmemN : ∀ x, x ∈ N ↔ ∃ c, ι c = x := fun x => by rw [hN, LinearMap.mem_ker]; exact hex x
  have hsmul : ∀ (p : P) (x : S ⊗[P] Ω[P⁄k]), algebraMap P S p • x = p • x := fun p x =>
      algebraMap_smul S p x
  let r : (S ⊗[P] Ω[P⁄k]) →ₗ[S] N :=
    { toFun := fun x => ⟨ι (l x), (hmemN _).mpr ⟨_, rfl⟩⟩
      map_add' := fun x y => by
        apply Subtype.ext
        change ι (l (x + y)) = ι (l x) + ι (l y)
        rw [map_add, map_add]
      map_smul' := fun s x => by
        obtain ⟨p, rfl⟩ := hPS s
        apply Subtype.ext
        change ι (l (algebraMap P S p • x)) = algebraMap P S p • ι (l x)
        rw [hsmul, map_smul, map_smul, hsmul] }
  have hr : ∀ n : N, r n = n := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmemN x).mp hx
    ext
    change ι (l (ι c)) = ι c
    rw [hlι]
  have hrincl : r ∘ₗ N.subtype = LinearMap.id := by ext n; exact congrArg Subtype.val (hr n) ▸ rfl
  have : IsNoetherianRing S := isNoetherianRing_of_surjective P S (algebraMap P S) hPS
  have : Module.Finite S (S ⊗[P] Ω[P⁄k]) := inferInstance
  have : Module.Finite (IsLocalRing.ResidueField S) ((IsLocalRing.ResidueField S) ⊗[S] (S ⊗[P]
      Ω[P⁄k])) := inferInstance
  set gK := g.baseChange (IsLocalRing.ResidueField S) with hgK
  set iK := N.subtype.baseChange (IsLocalRing.ResidueField S) with hiK
  have hgKs : Function.Surjective gK := by
    have := LinearMap.lTensor_surjective (IsLocalRing.ResidueField S) hgs
    intro y; obtain ⟨x, hx⟩ := this y; exact ⟨x, hx⟩
  have hexN : Function.Exact N.subtype g := by
    change Function.Exact g.ker.subtype g
    exact LinearMap.exact_subtype_ker_map g
  have hexK : Function.Exact iK gK := by
    have h := @lTensor_exact S N (S ⊗[P] Ω[P⁄k]) Ω[S⁄k]
      _ _ _ _ _ _ _ N.subtype g (IsLocalRing.ResidueField S) _ _ hexN hgs
    intro y
    exact h y
  have hiKinj : Function.Injective iK := by
    intro a b hab
    have := congrArg (r.baseChange (IsLocalRing.ResidueField S)) hab
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hrincl,
      LinearMap.baseChange_id, LinearMap.id_apply, LinearMap.id_apply] at this
    exact this
  have hdim := LinearMap.finrank_range_add_finrank_ker gK
  rw [LinearMap.range_eq_top.mpr hgKs, finrank_top, LinearMap.exact_iff.mp hexK] at hdim
  have hrange0 : Module.finrank (IsLocalRing.ResidueField S) (LinearMap.range iK) = 0 := by omega
  have hrange : LinearMap.range iK = ⊥ := Submodule.finrank_eq_zero.mp hrange0
  have hKN : ∀ x : (IsLocalRing.ResidueField S) ⊗[S] N, x = 0 := by
    intro x
    apply hiKinj
    rw [map_zero]
    have : iK x ∈ LinearMap.range iK := ⟨x, rfl⟩
    rwa [hrange, Submodule.mem_bot] at this
  have hNfg : N.FG := IsNoetherian.noetherian N
  have hNbot : N = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal S) N hNfg
    · have htop : (IsLocalRing.maximalIdeal S • ⊤ : Submodule S N) = ⊤ := by
        rw [eq_top_iff]
        intro n _
        have e := TensorProduct.quotTensorEquivQuotSMul N (IsLocalRing.maximalIdeal S)
        have h0 : e.symm (Submodule.Quotient.mk n) = 0 := hKN _
        have h1 := congrArg e h0
        rw [LinearEquiv.apply_symm_apply, map_zero] at h1
        exact (Submodule.Quotient.mk_eq_zero _).mp h1
      intro x hx
      have : (⟨x, hx⟩ : N) ∈ (IsLocalRing.maximalIdeal S • ⊤ : Submodule S N) := by
        rw [htop]
        exact Submodule.mem_top
      have := Submodule.mem_map_of_mem (f := N.subtype) this
      rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at this
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hcot : ∀ c : (RingHom.ker (algebraMap P S)).Cotangent, c = 0 := by
    intro c
    apply hιinj
    rw [map_zero]
    have : ι c ∈ N := (hmemN _).mpr ⟨c, rfl⟩
    rwa [hNbot, Submodule.mem_bot] at this
  set K : Ideal P := RingHom.ker (algebraMap P S) with hK
  have hKsq : K ≤ K • K := by
    intro x hx
    have := (Ideal.toCotangent_eq_zero K ⟨x, hx⟩).mp (hcot _)
    rwa [pow_two, ← Ideal.smul_eq_mul] at this
  have hKtop : K ≠ ⊤ := by
    intro h
    have : (1 : P) ∈ K := h ▸ Submodule.mem_top
    rw [hK, RingHom.mem_ker, map_one] at this
    exact one_ne_zero this
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot K K (IsNoetherian.noetherian K) hKsq
    (by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact IsLocalRing.le_maximalIdeal hKtop)

end AbelianVarieties.NOSProofs.CotangentKernel
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.SmoothMinimalPrimes

universe u

namespace MinimalPrimes

theorem isSmoothAt_of_forall_linearIndepOn_pow
    {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
        [IsReduced B]
    (p : ℕ) [ExpChar k p]
    (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔮 : 𝔮 ∈ minimalPrimes B)
    (H : ∀ s : Finset (Localization.AtPrime 𝔮), LinearIndepOn k _root_.id (s : Set
        (Localization.AtPrime 𝔮)) →
      LinearIndepOn k (· ^ p) (s : Set (Localization.AtPrime 𝔮))) :
    Algebra.IsSmoothAt k 𝔮 := by
  classical
  have hrad : ((⊥ : Ideal B).map (algebraMap B (Localization.AtPrime 𝔮))).radical =
      𝔮.map (algebraMap B (Localization.AtPrime 𝔮)) :=
    IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := Localization.AtPrime 𝔮) 𝔮 ⊥ h𝔮
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮) = ⊥ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← hrad, Ideal.map_bot]
    exact nilradical_eq_zero (Localization.AtPrime 𝔮)
  have hfield : IsField (Localization.AtPrime 𝔮) := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmax
  let : Field (Localization.AtPrime 𝔮) := hfield.toField
  have : Algebra.EssFiniteType k (Localization.AtPrime 𝔮) := inferInstance
  change Algebra.FormallySmooth k (Localization.AtPrime 𝔮)
  rcases expChar_is_prime_or_one k p with hprime | hp1
  swap
  · subst hp1
    have : CharZero k := charZero_of_expChar_one' k
    have : PerfectField k := PerfectField.ofCharZero
    exact Algebra.FormallySmooth.of_perfectField
  · obtain ⟨s, hs, hsep⟩ :=
      exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType p hprime H
    have : Algebra.IsSeparable
        ↥(IntermediateField.adjoin k (Set.range ((↑) : s → Localization.AtPrime 𝔮)))
            (Localization.AtPrime 𝔮) := by
      have hrange : Set.range ((↑) : s → Localization.AtPrime 𝔮) =
          (s : Set (Localization.AtPrime 𝔮)) := by
        ext x
        exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
      rw [hrange]
      exact hsep
    exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

end MinimalPrimes

theorem _root_.Algebra.isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField
    {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
        [IsReduced B]
    (S : Set (PrimeSpectrum B))
    (hdense : ∀ g : B, (∀ 𝔰 ∈ S, g ∈ 𝔰.asIdeal) → g = 0)
    (hsep : ∀ 𝔰 ∈ S, ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      Algebra.FormallySmooth k K ∧ Nonempty (𝔰.asIdeal.ResidueField →ₐ[k] K))
    (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔮 : 𝔮 ∈ minimalPrimes B) :
    Algebra.IsSmoothAt k 𝔮 := by
  classical
  obtain ⟨p, hp⟩ := ExpChar.exists k
  rcases hp with ⟨hp0⟩ | ⟨hpp, hpc⟩
  · have : ExpChar k 1 := ExpChar.zero
    apply MinimalPrimes.isSmoothAt_of_forall_linearIndepOn_pow 1 𝔮 h𝔮
    intro s hs
    have heq : (fun x : Localization.AtPrime 𝔮 => x ^ (1 : ℕ)) = _root_.id :=
      funext fun x => pow_one x
    rw [heq]
    exact hs
  · have : ExpChar k p := ExpChar.prime hpp
    refine MinimalPrimes.isSmoothAt_of_forall_linearIndepOn_pow p 𝔮 h𝔮 (fun s hs => ?_)
    refine Algebra.linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense p hpp S
        hdense
      (fun 𝔰 h𝔰 => ?_) 𝔮 h𝔮 s hs
    obtain ⟨K, iF, iA, hK, hne⟩ := hsep 𝔰 h𝔰
    exact ⟨K, iF, iA, fun t ht => @Algebra.FormallySmooth.linearIndepOn_pow_of_linearIndepOn_id k
        K _ iF iA hK p hpp _ t ht, hne⟩

end AbelianVarieties.NOSProofs.SmoothMinimalPrimes
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.SmoothFreeLocus

open TensorProduct

universe u

theorem _root_.Algebra.isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset
    {k : Type u} [Field k] {A : Type u} [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] (J : Ideal A)
    [Algebra k (A ⧸ J)] [Algebra.FiniteType k (A ⧸ J)] [IsReduced (A ⧸ J)]
    (S : Set (PrimeSpectrum (A ⧸ J)))
    (hdense : ∀ g : A ⧸ J, (∀ 𝔰 ∈ S, g ∈ 𝔰.asIdeal) → g = 0)
    (hsep : ∀ 𝔰 ∈ S, ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      Algebra.FormallySmooth k K ∧ Nonempty (𝔰.asIdeal.ResidueField →ₐ[k] K)) :
    IsOpen {𝔮 : PrimeSpectrum (A ⧸ J) | Algebra.IsSmoothAt k 𝔮.asIdeal ∧
      𝔮 ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M)} ∧
    ∀ 𝔮 : PrimeSpectrum (A ⧸ J), 𝔮.asIdeal ∈ minimalPrimes (A ⧸ J) →
      Algebra.IsSmoothAt k 𝔮.asIdeal ∧ 𝔮 ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M) := by
  classical
  have : Algebra.FinitePresentation k (A ⧸ J) := Algebra.FinitePresentation.of_finiteType.mp
      inferInstance
  refine ⟨?_, ?_⟩
  · have h1 : IsOpen (Algebra.smoothLocus k (A ⧸ J)) := Algebra.isOpen_smoothLocus
    have h2 : IsOpen (Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M)) := Module.isOpen_freeLocus
    have : {𝔮 : PrimeSpectrum (A ⧸ J) | Algebra.IsSmoothAt k 𝔮.asIdeal ∧
        𝔮 ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M)} =
        Algebra.smoothLocus k (A ⧸ J) ∩ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M) := by
      ext 𝔮; rfl
    rw [this]
    exact h1.inter h2
  · intro 𝔮 h𝔮
    refine ⟨Algebra.isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField S
        hdense hsep 𝔮.asIdeal h𝔮, ?_⟩
    rw [Module.mem_freeLocus]
    have : Ring.KrullDimLE 0 (Localization.AtPrime 𝔮.asIdeal) :=
      Ring.KrullDimLE.of_isLocalization 𝔮.asIdeal h𝔮 (Localization.AtPrime 𝔮.asIdeal)
    let hF : Field (Localization.AtPrime 𝔮.asIdeal) := Ring.KrullDimLE.isField_of_isReduced.toField
    exact Module.Free.of_divisionRing (Localization.AtPrime 𝔮.asIdeal) _

end AbelianVarieties.NOSProofs.SmoothFreeLocus
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_IsSmoothAt_of_isSmoothAt_of_smooth.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.SmoothDescent

universe u

open TensorProduct

namespace Descent

theorem projective_kaehlerDifferential_of_faithfullyFlat (R A B : Type u) [CommRing R] [CommRing
    A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Module.FinitePresentation A Ω[A⁄R]] [Module.FaithfullyFlat A B]
    [Algebra.FormallySmooth A B] [Algebra.FormallySmooth R B] :
    Module.Projective A Ω[A⁄R] := by
  have hex : Function.Exact (KaehlerDifferential.mapBaseChange R A B) (KaehlerDifferential.map R A
      B B) :=
    KaehlerDifferential.exact_mapBaseChange_map R A B
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange R A B) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B x).mp hx
    have : Subsingleton (Algebra.H1Cotangent A B) := Algebra.FormallySmooth.subsingleton_h1Cotangent
    rw [Subsingleton.elim y 0, map_zero]
  have hsurj : Function.Surjective (KaehlerDifferential.map R A B B) :=
      KaehlerDifferential.map_surjective R A B
  have : Module.Projective B Ω[B⁄A] := (Algebra.formallySmooth_iff A B).mp inferInstance |>.1
  have : Module.Projective B Ω[B⁄R] := (Algebra.formallySmooth_iff R B).mp inferInstance |>.1
  obtain ⟨l, hl⟩ := Module.projective_lifting_property (KaehlerDifferential.map R A B B)
      LinearMap.id hsurj
  obtain ⟨e, he₁, -⟩ := hex.splitSurjectiveEquiv hinj ⟨l, hl⟩
  have : Module.Projective B (B ⊗[A] Ω[A⁄R]) := by
    refine Module.Projective.of_split (KaehlerDifferential.mapBaseChange R A B)
      ((LinearMap.fst B _ _).comp e.toLinearMap) ?_
    rw [he₁]
    apply LinearMap.ext
    intro x
    change (e (e.symm (x, 0))).1 = x
    exact congrArg Prod.fst (e.apply_symm_apply (x, 0))
  have : Module.Flat A Ω[A⁄R] := Module.Flat.of_flat_tensorProduct A Ω[A⁄R] B
  exact Module.Flat.projective_of_finitePresentation

end Descent

theorem
    _root_.Algebra.IsSmoothAt.of_isSmoothAt_of_smooth (R S T : Type u) [CommRing R] [CommRing S]
        [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.FinitePresentation R S] [Algebra.Smooth S T] (𝔓 : Ideal T) [𝔓.IsPrime]
    (h : Algebra.IsSmoothAt R 𝔓) (𝔭 : Ideal S) [𝔭.IsPrime] (h𝔭 : 𝔓.under S = 𝔭) :
    Algebra.IsSmoothAt R 𝔭 := by
  subst h𝔭
  have : 𝔓.LiesOver (𝔓.under S) := ⟨rfl⟩
  let algAB : Algebra (Localization.AtPrime (𝔓.under S)) (Localization.AtPrime 𝔓) :=
    Localization.AtPrime.algebraOfLiesOver (𝔓.under S) 𝔓
  let A := Localization.AtPrime (𝔓.under S)
  let B := Localization.AtPrime 𝔓
  have : Algebra.FormallySmooth R B := h
  have : Module.Flat A B := inferInstance
  have : IsLocalHom (algebraMap A B) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom (𝔓.under S) 𝔓 (algebraMap S T)
        Ideal.LiesOver.over))
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : Algebra.FormallySmooth S B := inferInstance
  have : Algebra.FormallySmooth A B := Algebra.FormallySmooth.localization_base (𝔓.under
      S).primeCompl
  have : Algebra.FormallyEtale S A := Algebra.FormallyEtale.of_isLocalization (𝔓.under S).primeCompl
  have : Module.FinitePresentation A Ω[A⁄R] :=
    Module.FinitePresentation.of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S A)
  change Algebra.FormallySmooth R A
  rw [Algebra.formallySmooth_iff]
  refine ⟨Descent.projective_kaehlerDifferential_of_faithfullyFlat R A B, ?_⟩
  have eA : A ⊗[S] Algebra.H1Cotangent R S ≃ₗ[A] Algebra.H1Cotangent R A :=
    Algebra.tensorH1CotangentOfIsLocalization R A (𝔓.under S).primeCompl
  rw [← eA.toEquiv.subsingleton_congr]
  have e1 : B ⊗[A] (A ⊗[S] Algebra.H1Cotangent R S) ≃ₗ[B] B ⊗[T] (T ⊗[S] Algebra.H1Cotangent R S) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange S A B B (Algebra.H1Cotangent R S)
      ≪≫ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange S T B B (Algebra.H1Cotangent R
          S)).symm
  have eB : B ⊗[T] Algebra.H1Cotangent R T ≃ₗ[B] Algebra.H1Cotangent R B :=
    Algebra.tensorH1CotangentOfIsLocalization R B 𝔓.primeCompl
  have : Subsingleton (Algebra.H1Cotangent R B) := Algebra.FormallySmooth.subsingleton_h1Cotangent
  have : Module.Flat T B := inferInstance
  have hinj : Function.Injective
      (((Algebra.H1Cotangent.map R R S T).liftBaseChange T).baseChange B :
        B ⊗[T] (T ⊗[S] Algebra.H1Cotangent R S) →ₗ[B] B ⊗[T] Algebra.H1Cotangent R T) :=
    Module.Flat.lTensor_preserves_injective_linearMap _
      (Algebra.H1Cotangent.liftBaseChange_map_injective_of_smooth R S T)
  have : Subsingleton (B ⊗[A] (A ⊗[S] Algebra.H1Cotangent R S)) := by
    rw [e1.toEquiv.subsingleton_congr]
    exact (eB.toEquiv.injective.comp hinj).subsingleton
  exact Module.FaithfullyFlat.lTensor_reflects_triviality A B (A ⊗[S] Algebra.H1Cotangent R S)

end AbelianVarieties.NOSProofs.SmoothDescent
end
