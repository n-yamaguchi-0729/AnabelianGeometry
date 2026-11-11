/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Nyll.SchemeTheory.Divisors.DVRUnitQuotient
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Nyll.SchemeTheory.RingTheory.GenericFiber.Unramified
public import Nyll.SchemeTheory.RingTheory.Etale.UnramifiedDedekind
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Spectrum.Maximal.Topology
public import Mathlib.Topology.JacobsonSpace

/-!
# Principal divisors on an affine Dedekind domain

The finite-support and uniqueness assertions reuse Mathlib's factorization
of fractional ideals. The kernel consists exactly of the original ring units.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped nonZeroDivisors
open IsDedekindDomain

namespace FractionalIdeal
variable (R K : Type*) [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The finitely supported prime multiplicities of a fractional ideal. -/
def divisorFinsupp (I : FractionalIdeal R⁰ K) : HeightOneSpectrum R →₀ ℤ :=
  Finsupp.mk (finite_factors I).toFinset (fun v => count K v I)
    (fun _ => (finite_factors I).mem_toFinset)

@[simp] theorem divisorFinsupp_apply (I : FractionalIdeal R⁰ K)
    (v : HeightOneSpectrum R) : divisorFinsupp R K I v = count K v I := rfl

theorem divisorFinsupp_eq_iff {I J : FractionalIdeal R⁰ K}
    (hI : I ≠ 0) (hJ : J ≠ 0) :
    divisorFinsupp R K I = divisorFinsupp R K J ↔ I = J := by
  constructor
  · intro h
    have hc : ∀ v, count K v I = count K v J :=
      fun v => congrArg (fun d : HeightOneSpectrum R →₀ ℤ => d v) h
    rw [← finprod_heightOneSpectrum_factorization' K hI,
      ← finprod_heightOneSpectrum_factorization' K hJ]
    exact finprod_congr (fun v => congrArg (fun z : ℤ =>
      (v.asIdeal : FractionalIdeal R⁰ K) ^ z) (hc v))
  · intro h
    exact congrArg (divisorFinsupp R K) h

theorem divisorFinsupp_one : divisorFinsupp R K 1 = 0 := by
  apply Finsupp.ext
  intro v
  exact count_one K v

/-- The principal-divisor homomorphism on nonzero rational functions. -/
def principalDivisorAddHom : Additive Kˣ →+ (HeightOneSpectrum R →₀ ℤ) where
  toFun a := divisorFinsupp R K (spanSingleton R⁰ (a.toMul : K))
  map_zero' := by
    change divisorFinsupp R K (spanSingleton R⁰ (1 : K)) = 0
    rw [map_one, divisorFinsupp_one]
  map_add' a b := by
    apply Finsupp.ext
    intro v
    change count K v (spanSingleton R⁰ ((a.toMul : K) * (b.toMul : K))) =
      count K v (spanSingleton R⁰ (a.toMul : K)) +
        count K v (spanSingleton R⁰ (b.toMul : K))
    rw [map_mul]
    exact count_mul K v
      (spanSingleton_ne_zero_iff.mpr a.toMul.ne_zero)
      (spanSingleton_ne_zero_iff.mpr b.toMul.ne_zero)

/-- A nonzero rational function has zero divisor precisely when it is a
unit of the original Dedekind domain. -/
theorem principalDivisorAddHom_eq_zero_iff (a : Additive Kˣ) :
    principalDivisorAddHom R K a = 0 ↔
      ∃ u : Rˣ, Units.map (algebraMap R K).toMonoidHom u = a.toMul := by
  change divisorFinsupp R K (spanSingleton R⁰ (a.toMul : K)) = 0 ↔ _
  rw [← divisorFinsupp_one R K,
    divisorFinsupp_eq_iff R K (spanSingleton_ne_zero_iff.mpr a.toMul.ne_zero) one_ne_zero]
  rw [← map_one (spanSingleton R⁰ : K →*₀ FractionalIdeal R⁰ K)]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (spanSingleton_eq_spanSingleton (S := R⁰)).mp h.symm
    refine ⟨u, Units.ext ?_⟩
    change (algebraMap R K) (u : R) = (a.toMul : K)
    simpa only [Units.smul_def, Algebra.smul_def, mul_one] using hu
  · rintro ⟨u, hu⟩
    apply Eq.symm
    apply (spanSingleton_eq_spanSingleton (S := R⁰)).mpr
    refine ⟨u, ?_⟩
    have hv := congrArg (fun x : Kˣ => (x : K)) hu
    change (algebraMap R K) (u : R) = (a.toMul : K) at hv
    simpa only [Units.smul_def, Algebra.smul_def, mul_one] using hv

/-- A principal divisor can have coefficient one at any prescribed
height-one prime. The uniformizer comes from the existing adic valuation. -/
theorem exists_principalDivisorAddHom_apply_eq_one
    (v : HeightOneSpectrum R) :
    ∃ a : Additive Kˣ, principalDivisorAddHom R K a v = 1 := by
  obtain ⟨r, hr⟩ := v.intValuation_exists_uniformizer
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, map_zero] at hr
    exact WithZero.exp_ne_zero hr.symm
  have hrK : algebraMap R K r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr0
  refine ⟨Additive.ofMul (Units.mk0 (algebraMap R K r) hrK), ?_⟩
  change count K v (spanSingleton R⁰ (algebraMap R K r)) = 1
  rw [← coeIdeal_span_singleton]
  have hs : (Ideal.span ({r} : Set R)) ≠ 0 := by
    intro h
    exact hr0 (Ideal.span_singleton_eq_bot.mp h)
  rw [count_coe K v hs]
  rw [v.intValuation_if_neg hr0, WithZero.exp_inj, neg_inj] at hr
  exact hr

/-- Each individual prime coefficient of the principal-divisor map is
surjective. This makes no global assertion that all divisors are principal. -/
theorem principalDivisorAddHom_apply_surjective
    (v : HeightOneSpectrum R) :
    Function.Surjective (fun a : Additive Kˣ => principalDivisorAddHom R K a v) := by
  obtain ⟨a, ha⟩ := exists_principalDivisorAddHom_apply_eq_one R K v
  intro z
  refine ⟨z • a, ?_⟩
  change principalDivisorAddHom R K (z • a) v = z
  rw [map_zsmul, Finsupp.smul_apply, ha, zsmul_eq_mul, mul_one]
  rfl

/-- Every finite divisor agrees with a principal divisor on a basic
open neighbourhood of any prescribed height-one point. The element `s`
removes only the finitely many primes in their difference. -/
theorem exists_principalDivisor_eq_on_basicOpen
    (D : HeightOneSpectrum R →₀ ℤ) (v : HeightOneSpectrum R) :
    ∃ (a : Additive Kˣ) (s : R), s ∉ v.asIdeal ∧
      ∀ w : HeightOneSpectrum R, s ∉ w.asIdeal →
        principalDivisorAddHom R K a w = D w := by
  classical
  obtain ⟨a, ha⟩ := principalDivisorAddHom_apply_surjective R K v (D v)
  change principalDivisorAddHom R K a v = D v at ha
  let E := D - principalDivisorAddHom R K a
  have hv : E v = 0 := by
    change D v - principalDivisorAddHom R K a v = 0
    rw [ha, sub_self]
  let I : Ideal R := ∏ w ∈ E.support, w.asIdeal
  have hI : ¬ I ≤ v.asIdeal := by
    intro h
    obtain ⟨w, hw, hwv⟩ := v.isPrime.prod_le.mp h
    have he : w = v :=
      HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top hwv)
    have hne : E v ≠ 0 := Finsupp.mem_support_iff.mp (he ▸ hw)
    exact hne hv
  obtain ⟨s, hsI, hsv⟩ := Set.not_subset.mp hI
  refine ⟨a, s, hsv, ?_⟩
  intro w hsw
  have hw : w ∉ E.support := by
    intro hw
    have hIw : I ≤ w.asIdeal :=
      Ideal.prod_le_inf.trans (Finset.inf_le hw)
    exact hsw (hIw hsI)
  have hw0 : E w = 0 := Finsupp.notMem_support_iff.mp hw
  change D w - principalDivisorAddHom R K a w = 0 at hw0
  exact (sub_eq_zero.mp hw0).symm

/-- The principal-divisor coordinate is the additive exponent of the
existing adic valuation, with the usual opposite sign convention. -/
theorem valuation_eq_exp_neg_principalDivisor
    (v : HeightOneSpectrum R) (a : Additive Kˣ) :
    v.valuation K (a.toMul : K) =
      WithZero.exp (-(principalDivisorAddHom R K a v)) := by
  obtain ⟨r, s, hrs⟩ := IsLocalization.exists_mk'_eq R⁰ (a.toMul : K)
  have hr0 : r ≠ 0 := by
    intro hr
    apply a.toMul.ne_zero
    rw [← hrs, hr, IsFractionRing.mk'_eq_div, map_zero, zero_div]
  have hs0 : (s : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s.property
  have hI : spanSingleton R⁰ (a.toMul : K) =
      spanSingleton R⁰ ((algebraMap R K) (s : R))⁻¹ *
        (Ideal.span ({r} : Set R) : FractionalIdeal R⁰ K) := by
    rw [coeIdeal_span_singleton, ← map_mul]
    apply congrArg (spanSingleton R⁰)
    rw [← hrs, IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  have hc := count_well_defined K v
    (spanSingleton_ne_zero_iff.mpr a.toMul.ne_zero) hI
  change v.valuation K (a.toMul : K) =
    WithZero.exp (-count K v (spanSingleton R⁰ (a.toMul : K)))
  rw [hc, ← hrs, v.valuation_of_mk', v.intValuation_if_neg hr0,
    v.intValuation_if_neg hs0, ← WithZero.exp_sub]
  congr 1
  omega

/-- A uniformizer of the actual valuation ring has principal-divisor
coefficient one at the corresponding height-one point. -/
theorem principalDivisor_apply_eq_one_of_irreducible
    (v : HeightOneSpectrum R)
    (π : (v.valuation K).valuationSubring) (hπ : Irreducible π)
    (a : Additive Kˣ) (ha : (a.toMul : K) = (π : K)) :
    principalDivisorAddHom R K a v = 1 := by
  have hU := Valuation.isUniformizer_of_maximalIdeal_eq_span
    (v.valuation K) ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ)
  have hv : v.valuation K (π : K) = WithZero.exp (-1 : ℤ) := by
    rw [hU, Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuation_surjective K)]
    rfl
  have hx := valuation_eq_exp_neg_principalDivisor R K v a
  rw [ha, hv] at hx
  have hn : -(principalDivisorAddHom R K a v) = -(1 : ℤ) :=
    WithZero.exp_inj.mp hx.symm
  exact neg_injective hn

/-- Zero principal-divisor coefficient is exactly valuation one. -/
theorem principalDivisor_apply_eq_zero_iff_valuation_eq_one
    (v : HeightOneSpectrum R) (a : Additive Kˣ) :
    principalDivisorAddHom R K a v = 0 ↔ v.valuation K (a.toMul : K) = 1 := by
  rw [valuation_eq_exp_neg_principalDivisor R K v a, ← WithZero.exp_zero,
    WithZero.exp_inj, neg_eq_zero]

/-- Vanishing at a height-one point means that the rational function
belongs to the unit group of its actual valuation subring. -/
theorem principalDivisor_apply_eq_zero_iff_mem_localUnitGroup
    (v : HeightOneSpectrum R) (a : Additive Kˣ) :
    principalDivisorAddHom R K a v = 0 ↔
      a.toMul ∈ (HeightOneSpectrum.valuationSubringAtPrime K v).unitGroup := by
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.mem_unitGroup_iff]
  exact principalDivisor_apply_eq_zero_iff_valuation_eq_one R K v a

section CokernelOrder

universe u

variable (R K : Type u) [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Extract the principal-divisor coefficient at the original height-one prime. -/
def principalDivisorCoefficientAt
    (v : HeightOneSpectrum R) : Additive Kˣ →+ ℤ :=
  (Finsupp.lapply (R := ℤ) v).toAddMonoidHom.comp (principalDivisorAddHom R K)

/-- The principal-divisor coefficient descends to the cokernel of units of
the actual valuation ring at a height-one point. -/
def principalDivisorUnitCokernelOrder (v : HeightOneSpectrum R) :
    cokernel (IsDiscreteValuationRing.fractionUnitInclusion
      (v.valuation K).valuationSubring K) ⟶
        (AddCommGrpCat.of (ULift.{u} ℤ) : AddCommGrpCat.{u}) := by
  let A := (v.valuation K).valuationSubring
  let q := (AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ).symm.toAddMonoidHom.comp
    (principalDivisorCoefficientAt R K v)
  have hkill : IsDiscreteValuationRing.fractionUnitInclusion A K ≫
      AddCommGrpCat.ofHom q = 0 := by
    apply AddCommGrpCat.hom_ext
    ext x
    let uK : Kˣ := Units.map (algebraMap A K).toMonoidHom x.toMul
    have heq : uK = A.unitGroupMulEquiv.symm x.toMul := by
      apply Units.ext
      change (algebraMap A K) (x.toMul.val) =
        ((A.unitGroupMulEquiv.symm x.toMul : A.unitGroup) : Kˣ)
      rfl
    have hu : uK ∈ A.unitGroup := by
      rw [heq]
      exact (A.unitGroupMulEquiv.symm x.toMul).property
    change principalDivisorAddHom R K (Additive.ofMul uK) v = 0
    apply (principalDivisor_apply_eq_zero_iff_mem_localUnitGroup R K v _).2
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact hu
  exact cokernel.desc _ (AddCommGrpCat.ofHom q) hkill

/-- The actual cokernel projection followed by the order map is the
principal-divisor coefficient at the chosen height-one point. -/
theorem principalDivisorUnitCokernelOrder_π (v : HeightOneSpectrum R) :
    cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion
      (v.valuation K).valuationSubring K) ≫
        principalDivisorUnitCokernelOrder R K v =
      AddCommGrpCat.ofHom ((AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ).symm.toAddMonoidHom.comp
        (principalDivisorCoefficientAt R K v)) := by
  exact cokernel.π_desc _ _ _

/-- The ordinary integer-valued additive hom underlying the categorical order. -/
def principalDivisorUnitCokernelOrderHom (v : HeightOneSpectrum R) :
    (cokernel (IsDiscreteValuationRing.fractionUnitInclusion
      (v.valuation K).valuationSubring K) : AddCommGrpCat.{u}) →+ ℤ :=
  (AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ).toAddMonoidHom.comp
    (principalDivisorUnitCokernelOrder R K v).hom

/-- Evaluation of the order map on a projected fraction-field unit is its
principal-divisor coefficient. -/
theorem principalDivisorUnitCokernelOrder_apply
    (v : HeightOneSpectrum R) (a : Additive Kˣ) :
    principalDivisorUnitCokernelOrderHom R K v
      ((cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion
        (v.valuation K).valuationSubring K)).hom a) =
    principalDivisorAddHom R K a v := by
  have h := ConcreteCategory.congr_hom
    (principalDivisorUnitCokernelOrder_π R K v) a
  change (principalDivisorUnitCokernelOrder R K v).hom
      ((cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion
        (v.valuation K).valuationSubring K)).hom a) =
    ULift.up (principalDivisorAddHom R K a v) at h
  exact congrArg (fun z : ULift.{u} ℤ => z.down) h

/-- Composing the order map with the uniformizer normalization is the
identity on `ℤ`. -/
theorem principalDivisorUnitCokernelOrder_comp_fractionUnitCokernelEquiv
    (v : HeightOneSpectrum R)
    (π : (v.valuation K).valuationSubring) (hπ : Irreducible π)
    (πK : Kˣ) (hπK : (πK : K) = (π : K)) :
    (principalDivisorUnitCokernelOrderHom R K v).comp
      (IsDiscreteValuationRing.fractionUnitCokernelEquiv
        (v.valuation K).valuationSubring K hπ πK hπK).toAddMonoidHom =
      AddMonoidHom.id ℤ := by
  let A := (v.valuation K).valuationSubring
  let e := IsDiscreteValuationRing.fractionUnitCokernelEquiv A K hπ πK hπK
  have hcoeff := principalDivisor_apply_eq_one_of_irreducible R K v π hπ
    (Additive.ofMul πK) hπK
  have hproj := principalDivisorUnitCokernelOrder_apply R K v
    (Additive.ofMul πK)
  have hproj' := hproj
  apply AddMonoidHom.ext
  intro n
  change principalDivisorUnitCokernelOrderHom R K v (e n) = n
  change principalDivisorUnitCokernelOrderHom R K v
    (n • (cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion A K)).hom
      (Additive.ofMul πK)) = n
  rw [map_zsmul]
  rw [zsmul_eq_mul]
  calc
    n * principalDivisorUnitCokernelOrderHom R K v
        ((cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion A K)).hom
          (Additive.ofMul πK)) =
        n * principalDivisorAddHom R K (Additive.ofMul πK) v := by
      exact congrArg (fun z : ℤ => n * z) hproj'
    _ = n := by rw [hcoeff, mul_one]

/-- The principal-divisor order map from the actual valuation-ring unit
cokernel is an isomorphism with `ℤ`. -/
theorem principalDivisorUnitCokernelOrder_isIso (v : HeightOneSpectrum R) :
    IsIso (principalDivisorUnitCokernelOrder R K v) := by
  let A := (v.valuation K).valuationSubring
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  let πK : Kˣ := Units.mk0 (π : K) (by
    intro hz
    exact hπ.ne_zero (Subtype.ext hz))
  let e := IsDiscreteValuationRing.fractionUnitCokernelEquiv A K hπ πK rfl
  have hcomp := principalDivisorUnitCokernelOrder_comp_fractionUnitCokernelEquiv
    R K v π hπ πK rfl
  have hfun : principalDivisorUnitCokernelOrderHom R K v =
      e.symm.toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro x
    obtain ⟨n, rfl⟩ := e.surjective x
    calc
      principalDivisorUnitCokernelOrderHom R K v (e n) = n :=
        congrArg (fun f : ℤ →+ ℤ => f n) hcomp
      _ = e.symm.toAddMonoidHom (e n) := (e.symm_apply_apply n).symm
  have hbij : Function.Bijective (principalDivisorUnitCokernelOrderHom R K v) := by
    rw [hfun]
    exact e.symm.bijective
  apply (ConcreteCategory.isIso_iff_bijective
    (principalDivisorUnitCokernelOrder R K v)).mpr
  change Function.Bijective
    (fun x => ULift.up (principalDivisorUnitCokernelOrderHom R K v x))
  exact ULift.up_bijective.comp hbij

end CokernelOrder

section PrincipalDivisorNaturality

universe u

variable (R S K L : Type u)
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
  [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum S)
  [Algebra ((v.valuation K).valuationSubring)
    ((w.valuation L).valuationSubring)]
  [IsLocalHom (algebraMap (v.valuation K).valuationSubring
    (w.valuation L).valuationSubring)]
  [Algebra.EssFiniteType ((v.valuation K).valuationSubring)
    ((w.valuation L).valuationSubring)]
  [Algebra.FormallyUnramified ((v.valuation K).valuationSubring)
    ((w.valuation L).valuationSubring)]
  (g : K →+* L)
  (h : g.comp (algebraMap (v.valuation K).valuationSubring K) =
    (algebraMap (w.valuation L).valuationSubring L).comp
      (algebraMap (v.valuation K).valuationSubring
        (w.valuation L).valuationSubring))

include h

/-- Principal-divisor coefficients are preserved by the actual local map on
valuation rings when that map is essentially finite type and unramified. -/
theorem principalDivisorAddHom_map_eq_of_unramifiedLocal
    (a : Additive Kˣ) :
    principalDivisorAddHom S L
      ((Units.map g.toMonoidHom).toAdditive a) w =
    principalDivisorAddHom R K a v := by
  let A := (v.valuation K).valuationSubring
  let B := (w.valuation L).valuationSubring
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hρ : Irreducible (algebraMap A B π) :=
    IsDiscreteValuationRing.algebraMap_irreducible_of_unramified_local
      A B hπ
  let πK : Kˣ := Units.mk0 (algebraMap A K π) (by
    intro hz
    exact hπ.ne_zero ((IsFractionRing.injective A K)
      (hz.trans (map_zero _).symm)))
  let ρL : Lˣ := Units.map g.toMonoidHom πK
  have hρL : (ρL : L) = algebraMap B L (algebraMap A B π) :=
    RingHom.congr_fun h π
  let eA := IsDiscreteValuationRing.fractionUnitCokernelEquiv A K hπ πK rfl
  let eB := IsDiscreteValuationRing.fractionUnitCokernelEquiv B L hρ ρL hρL
  let M := IsDiscreteValuationRing.fractionUnitCokernelMap
    A K B L (algebraMap A B) g h
  have hM (n : ℤ) : M.hom (eA n) = eB n :=
    IsDiscreteValuationRing.fractionUnitCokernelMap_equiv_apply
      A K B L (algebraMap A B) g h hπ πK rfl hρ ρL hρL rfl n
  have hnormA :
      (principalDivisorUnitCokernelOrderHom R K v).comp eA.toAddMonoidHom =
        AddMonoidHom.id ℤ :=
    principalDivisorUnitCokernelOrder_comp_fractionUnitCokernelEquiv
      R K v π hπ πK rfl
  have hnormB :
      (principalDivisorUnitCokernelOrderHom S L w).comp eB.toAddMonoidHom =
        AddMonoidHom.id ℤ :=
    principalDivisorUnitCokernelOrder_comp_fractionUnitCokernelEquiv
      S L w (algebraMap A B π) hρ ρL hρL
  have horder :
      (principalDivisorUnitCokernelOrderHom S L w).comp M.hom =
        principalDivisorUnitCokernelOrderHom R K v := by
    ext x
    obtain ⟨n, rfl⟩ := eA.surjective x
    calc
      principalDivisorUnitCokernelOrderHom S L w (M.hom (eA n)) =
          principalDivisorUnitCokernelOrderHom S L w (eB n) :=
        congrArg (principalDivisorUnitCokernelOrderHom S L w) (hM n)
      _ = n := congrArg (fun q : ℤ →+ ℤ => q n) hnormB
      _ = principalDivisorUnitCokernelOrderHom R K v (eA n) :=
        (congrArg (fun q : ℤ →+ ℤ => q n) hnormA).symm
  have hproj : M.hom
      ((cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion A K)).hom a) =
      (cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion B L)).hom
        ((Units.map g.toMonoidHom).toAdditive a) := by
    have hp := ConcreteCategory.congr_hom
      (IsDiscreteValuationRing.fractionUnitCokernelMap_π
        A K B L (algebraMap A B) g h) a
    simpa only [M, AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom,
      AddMonoidHom.coe_comp, Function.comp_apply] using hp
  have horderAtProjection := congrArg
    (fun q : (cokernel (IsDiscreteValuationRing.fractionUnitInclusion A K) :
      AddCommGrpCat.{u}) →+ ℤ =>
        q ((cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion A K)).hom a))
    horder
  calc
    principalDivisorAddHom S L ((Units.map g.toMonoidHom).toAdditive a) w =
        principalDivisorUnitCokernelOrderHom S L w
          ((cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion B L)).hom
            ((Units.map g.toMonoidHom).toAdditive a)) :=
      (principalDivisorUnitCokernelOrder_apply S L w
        ((Units.map g.toMonoidHom).toAdditive a)).symm
    _ = principalDivisorUnitCokernelOrderHom S L w
          (M.hom
            ((cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion A K)).hom a)) :=
      congrArg (principalDivisorUnitCokernelOrderHom S L w) hproj.symm
    _ = principalDivisorUnitCokernelOrderHom R K v
          ((cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion A K)).hom a) :=
      horderAtProjection
    _ = principalDivisorAddHom R K a v :=
      principalDivisorUnitCokernelOrder_apply R K v a

end PrincipalDivisorNaturality

/-- A zero divisor coefficient supplies an actual local unit lifting the
rational function, not merely a numerical valuation equality. -/
theorem exists_localUnit_of_principalDivisor_apply_eq_zero
    (v : HeightOneSpectrum R) (a : Additive Kˣ)
    (ha : principalDivisorAddHom R K a v = 0) :
    ∃ u : (HeightOneSpectrum.valuationSubringAtPrime K v)ˣ,
      Units.map (algebraMap (HeightOneSpectrum.valuationSubringAtPrime K v) K).toMonoidHom u =
        a.toMul := by
  let A := HeightOneSpectrum.valuationSubringAtPrime K v
  let b : A.unitGroup := ⟨a.toMul,
    (principalDivisor_apply_eq_zero_iff_mem_localUnitGroup R K v a).mp ha⟩
  refine ⟨A.unitGroupMulEquiv b, Units.ext ?_⟩
  exact A.coe_unitGroupMulEquiv_apply b

/-- A finite divisor vanishes on a nonempty basic open containing the
generic point. -/
theorem exists_nonzero_basicOpen_divisor_vanishes
    (D : HeightOneSpectrum R →₀ ℤ) :
    ∃ s : R, s ≠ 0 ∧ ∀ w : HeightOneSpectrum R, s ∉ w.asIdeal → D w = 0 := by
  classical
  let I : Ideal R := ∏ w ∈ D.support, w.asIdeal
  have hI : I ≠ ⊥ := by
    apply Finset.prod_ne_zero_iff.mpr
    intro w hw
    exact w.ne_bot
  obtain ⟨s, hsI, hs0⟩ := I.ne_bot_iff.mp hI
  refine ⟨s, hs0, ?_⟩
  intro w hsw
  apply Finsupp.notMem_support_iff.mp
  intro hw
  exact hsw ((Ideal.prod_le_inf.trans (Finset.inf_le hw)) hsI)

/-- Every point, including the generic point, has a basic neighborhood
on which a finite divisor is represented by one rational function. -/
theorem exists_principalDivisor_eq_on_basicOpen_at_prime
    (D : HeightOneSpectrum R →₀ ℤ) (p : PrimeSpectrum R) :
    ∃ (s : R) (a : Additive Kˣ), s ∉ p.asIdeal ∧
      ∀ v : HeightOneSpectrum R, s ∉ v.asIdeal →
        principalDivisorAddHom R K a v = D v := by
  by_cases hp : p.asIdeal = ⊥
  · obtain ⟨s, hs, hD⟩ := exists_nonzero_basicOpen_divisor_vanishes R D
    refine ⟨s, 0, ?_, ?_⟩
    · rw [hp, Ideal.mem_bot]
      exact hs
    · intro v hv
      rw [map_zero, Finsupp.zero_apply, hD v hv]
  · let v : HeightOneSpectrum R := ⟨p.asIdeal, p.isPrime, hp⟩
    obtain ⟨a, s, hs, ha⟩ := exists_principalDivisor_eq_on_basicOpen R K D v
    exact ⟨s, a, hs, ha⟩
universe v

private theorem valuationSubring_cast_val {F : Type v} [Field F]
    (V W : ValuationSubring F) (h : V = W) (x : V) :
    ((RingEquiv.cast (R := fun T : ValuationSubring F => T) h x : W) : F) = (x : F) := by
  subst W
  rfl
/-- Principal-divisor coefficients are preserved under an essentially finite type,
unramified base extension. -/
theorem principalDivisorAddHom_map_eq_of_base_unramified
    {R S K L : Type v} [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S] [Algebra R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra S L] [IsFractionRing S L]
    (g : K →+* L)
    (hg : g.comp (algebraMap R K) = (algebraMap S L).comp (algebraMap R S))
    (v : IsDedekindDomain.HeightOneSpectrum R) (w : IsDedekindDomain.HeightOneSpectrum S)
    (hwv : w.asIdeal.under R = v.asIdeal) (a : Additive Kˣ) :
    principalDivisorAddHom S L ((Units.map g.toMonoidHom).toAdditive a) w =
      principalDivisorAddHom R K a v := by
  let p := v.asIdeal
  let q := w.asIdeal
  let hpPrime : p.IsPrime := v.isPrime
  let hqPrime : q.IsPrime := w.isPrime
  let hLiesOver : q.LiesOver p := ⟨hwv.symm⟩
  let VA := (v.valuation K).valuationSubring
  let VB := (w.valuation L).valuationSubring
  let VA₀ := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v
  let VB₀ := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L w
  have hVA : VA₀ = VA :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring (v := v)
  have hVB : VB₀ = VB :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring (v := w)
  let A₀ := Localization.AtPrime p
  let B₀ := Localization.AtPrime q
  let hAlgA₀B₀ : Algebra A₀ B₀ := Localization.AtPrime.algebraOfLiesOver p q
  let eA₀ : A₀ ≃ₐ[R] VA₀ := IsLocalization.algEquiv p.primeCompl A₀ VA₀
  let eB₀ : B₀ ≃ₐ[S] VB₀ := IsLocalization.algEquiv q.primeCompl B₀ VB₀
  let eVA : VA₀ ≃+* VA := RingEquiv.cast (R := fun T : ValuationSubring K => T) hVA
  let eVB : VB₀ ≃+* VB := RingEquiv.cast (R := fun T : ValuationSubring L => T) hVB
  let eA : A₀ ≃+* VA := eA₀.toRingEquiv.trans eVA
  let eB : B₀ ≃+* VB := eB₀.toRingEquiv.trans eVB
  let f₀ : A₀ →+* B₀ := algebraMap A₀ B₀
  let fV : VA →+* VB := eB.toRingHom.comp (f₀.comp eA.symm.toRingHom)
  let jA : A₀ →+* K := VA₀.subtype.comp eA₀.toRingHom
  let jB : B₀ →+* L := VB₀.subtype.comp eB₀.toRingHom
  have hfbase (r : R) :
      f₀ (algebraMap R A₀ r) = algebraMap S B₀ (algebraMap R S r) := by
    change algebraMap A₀ B₀ (algebraMap R A₀ r) = _
    rw [← IsScalarTower.algebraMap_apply R A₀ B₀,
      IsScalarTower.algebraMap_apply R S B₀]
  have hLoc : jB.comp f₀ = g.comp jA := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext r
    change jB (f₀ (algebraMap R A₀ r)) = g (jA (algebraMap R A₀ r))
    calc
      jB (f₀ (algebraMap R A₀ r)) =
          jB (algebraMap S B₀ (algebraMap R S r)) :=
        congrArg jB (hfbase r)
      _ = algebraMap S L (algebraMap R S r) := by
        change ((eB₀ (algebraMap S B₀ (algebraMap R S r)) : VB₀) : L) = _
        rw [eB₀.commutes]
        change algebraMap VB₀ L (algebraMap S VB₀ (algebraMap R S r)) = _
        rw [← IsScalarTower.algebraMap_apply S VB₀ L]
      _ = g (algebraMap R K r) := (RingHom.congr_fun hg r).symm
      _ = g (jA (algebraMap R A₀ r)) := by
        change g (algebraMap R K r) =
          g (VA₀.subtype (eA₀ (algebraMap R A₀ r)))
        rw [eA₀.commutes]
        change g (algebraMap R K r) =
          g (algebraMap VA₀ K (algebraMap R VA₀ r))
        rw [← IsScalarTower.algebraMap_apply R VA₀ K]
  let hAlgVAVB : Algebra VA VB := fV.toAlgebra
  have hfvalA (x : VA) : jA (eA.symm x) = x := by
    change (VA₀.subtype.comp eA₀.toRingHom) (eA₀.symm (eVA.symm x)) = x
    calc
      (VA₀.subtype.comp eA₀.toRingHom) (eA₀.symm (eVA.symm x)) =
          (eA (eA.symm x) : K) :=
        (valuationSubring_cast_val VA₀ VA hVA (eA₀ (eA.symm x))).symm
      _ = (x : K) := congrArg (fun z : VA => (z : K)) (eA.apply_symm_apply x)
  have hfvalB (x : VB) : jB (eB.symm x) = x := by
    change (VB₀.subtype.comp eB₀.toRingHom) (eB₀.symm (eVB.symm x)) = x
    calc
      (VB₀.subtype.comp eB₀.toRingHom) (eB₀.symm (eVB.symm x)) =
          (eB (eB.symm x) : L) :=
        (valuationSubring_cast_val VB₀ VB hVB (eB₀ (eB.symm x))).symm
      _ = (x : L) := congrArg (fun z : VB => (z : L)) (eB.apply_symm_apply x)
  have hSquare : g.comp (algebraMap VA K) = (algebraMap VB L).comp fV := by
    ext x
    have hloc := RingHom.congr_fun hLoc (eA.symm x)
    change jB (f₀ (eA.symm x)) = g (jA (eA.symm x)) at hloc
    have hleft : jB (f₀ (eA.symm x)) = (fV x : L) := by
      have hb := hfvalB (fV x)
      have hsymm : eB.symm (fV x) = f₀ (eA.symm x) := by
        change eB.symm (eB (f₀ (eA.symm x))) = _
        exact eB.symm_apply_apply _
      rw [hsymm] at hb
      exact hb
    calc
      g (x : K) = g (jA (eA.symm x)) := congrArg g (hfvalA x).symm
      _ = jB (f₀ (eA.symm x)) := hloc.symm
      _ = (fV x : L) := hleft
  have hlocal : IsLocalHom fV := by
    have hA₀ : IsLocalHom eA.symm := inferInstance
    have hA : IsLocalHom eA.symm.toRingHom :=
      ⟨fun a ha => hA₀.map_nonunit a ha⟩
    have hB₀ : IsLocalHom eB := inferInstance
    have hB : IsLocalHom eB.toRingHom :=
      ⟨fun a ha => hB₀.map_nonunit a ha⟩
    have h1 : IsLocalHom (f₀.comp eA.symm.toRingHom) :=
      RingHom.isLocalHom_comp f₀ eA.symm.toRingHom
    exact RingHom.isLocalHom_comp eB.toRingHom (f₀.comp eA.symm.toRingHom)
  let hLocalMap : IsLocalHom (algebraMap VA VB) := hlocal
  let hAlgA₀VA : Algebra A₀ VA := eA.toRingHom.toAlgebra
  let hAlgA₀VB : Algebra A₀ VB := (fV.comp eA.toRingHom).toAlgebra
  let hTowerA₀VAVB : IsScalarTower A₀ VA VB := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let hAlgB₀VB : Algebra B₀ VB := eB.toRingHom.toAlgebra
  let hTowerA₀B₀VB : IsScalarTower A₀ B₀ VB := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change eB (f₀ (eA.symm (eA x))) = eB (f₀ x)
    rw [eA.symm_apply_apply]
  have hET_RB₀ : Algebra.EssFiniteType R B₀ := Algebra.EssFiniteType.comp R S B₀
  have hET_A₀B₀ : Algebra.EssFiniteType A₀ B₀ := Algebra.EssFiniteType.of_comp R A₀ B₀
  have hFU_RB₀ : Algebra.FormallyUnramified R B₀ := Algebra.FormallyUnramified.comp R S B₀
  have hFU_A₀B₀ : Algebra.FormallyUnramified A₀ B₀ :=
    Algebra.FormallyUnramified.of_restrictScalars R A₀ B₀
  have eBalg : B₀ ≃ₐ[B₀] VB :=
    AlgEquiv.ofRingEquiv (R := B₀) (f := eB) (fun x => by rfl)
  have hET_B₀VB : Algebra.EssFiniteType B₀ VB :=
    Algebra.EssFiniteType.of_surjective eBalg.toAlgHom eBalg.surjective
  have hFU_B₀VB : Algebra.FormallyUnramified B₀ VB :=
    Algebra.FormallyUnramified.of_surjective eBalg.toAlgHom eBalg.surjective
  have hET_A₀VB : Algebra.EssFiniteType A₀ VB := Algebra.EssFiniteType.comp A₀ B₀ VB
  have hFU_A₀VB : Algebra.FormallyUnramified A₀ VB :=
    Algebra.FormallyUnramified.comp A₀ B₀ VB
  have hET_VAVB : Algebra.EssFiniteType VA VB := Algebra.EssFiniteType.of_comp A₀ VA VB
  have hFU_VAVB : Algebra.FormallyUnramified VA VB :=
    Algebra.FormallyUnramified.of_restrictScalars A₀ VA VB
  have hLocalAlgebraMap : IsLocalHom (algebraMap VA VB) := hlocal
  exact principalDivisorAddHom_map_eq_of_unramifiedLocal
    R S K L v w g hSquare a


end FractionalIdeal

namespace ValuationSubring

variable {K B : Type*} [Field K] [CommRing B] [IsDomain B]

/-- A local map out of a valuation ring reflects rational units after passing
to fraction fields. -/
theorem mem_unitGroup_of_fraction_image_unit
    (A : ValuationSubring K) (g : A →+* B) [IsLocalHom g]
    (f : K →+* FractionRing B)
    (hfg : (algebraMap B (FractionRing B)).comp g =
      f.comp A.subtype)
    (a : Kˣ) (u : Bˣ)
    (hu : f (a : K) = algebraMap B (FractionRing B) (u : B)) :
    a ∈ A.unitGroup := by
  have hmem (b : Kˣ) (w : Bˣ)
      (hb : (b : K) ∈ A)
      (hw : f (b : K) = algebraMap B (FractionRing B) (w : B)) :
      b ∈ A.unitGroup := by
    let x : A := ⟨(b : K), hb⟩
    have hg : g x = (w : B) := by
      apply IsFractionRing.injective B (FractionRing B)
      exact (RingHom.congr_fun hfg x).trans hw
    have hx : IsUnit x := IsLocalHom.map_nonunit (f := g) x (by
      rw [hg]
      exact w.isUnit)
    obtain ⟨z, hz⟩ := hx
    have heq : ((A.unitGroupMulEquiv.symm z : A.unitGroup) : Kˣ) = b := by
      apply Units.ext
      change ((z : A) : K) = (b : K)
      exact congrArg (fun y : A => (y : K)) hz
    rw [← heq]
    exact (A.unitGroupMulEquiv.symm z).property
  rcases A.mem_or_inv_mem (a : K) with ha | ha
  · exact hmem a u ha hu
  · have hi : (a⁻¹ : Kˣ) ∈ A.unitGroup := by
      have ha' : ((a⁻¹ : Kˣ) : K) ∈ A := by simpa using ha
      apply hmem (a⁻¹) (u⁻¹) ha'
      rw [map_units_inv f a, hu]
      exact (map_units_inv (algebraMap B (FractionRing B)) u).symm
    exact (A.unitGroup.inv_mem_iff).mp hi

end ValuationSubring

section AffineEtaleDivisorPullback

open IsDedekindDomain

variable {R S : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDomain S] [Algebra R S] [Algebra.Etale R S]

/-- The height-one prime map induced by contraction along an affine etale
map of Dedekind domains. -/
noncomputable def heightOneSpectrumContractionOfEtale
    (w : HeightOneSpectrum S) : HeightOneSpectrum R :=
  ⟨w.asIdeal.under R, Ideal.IsPrime.under R w.asIdeal,
    EtaleFundamentalGroups.heightOne_contraction_ne_bot_of_etale
      (R := R) (S := S) (K := FractionRing R) w⟩

@[simp] theorem heightOneSpectrumContractionOfEtale_asIdeal
    (w : HeightOneSpectrum S) :
    (heightOneSpectrumContractionOfEtale w).asIdeal = w.asIdeal.under R := rfl

end AffineEtaleDivisorPullback

section HeightOneSpectrumContractionComposition

open IsDedekindDomain

variable {R S : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra.Etale R S]

/-- Contraction of height-one primes is compatible with composition of affine
étale maps. -/
theorem heightOneSpectrumContractionOfEtale_comp
    {T : Type*}
    [CommRing T] [IsDomain T]
    [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.Etale S T] [Algebra.Etale R T]
    (w : HeightOneSpectrum T) :
    heightOneSpectrumContractionOfEtale (R := R) (S := S)
      (heightOneSpectrumContractionOfEtale (R := S) (S := T) w) =
    heightOneSpectrumContractionOfEtale (R := R) (S := T) w := by
  apply HeightOneSpectrum.ext
  simp only [heightOneSpectrumContractionOfEtale_asIdeal]
  change Ideal.comap (algebraMap R S)
      (Ideal.comap (algebraMap S T) w.asIdeal) =
    Ideal.comap (algebraMap R T) w.asIdeal
  rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]

end HeightOneSpectrumContractionComposition

section AffineEtaleDivisorPullback

open IsDedekindDomain

variable {R S : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDomain S] [Algebra R S] [Algebra.Etale R S]

/-- Contraction along the identity algebra map fixes every height-one prime. -/
theorem heightOneSpectrumContractionOfEtale_id
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R R] [Algebra.Etale R R]
    (hmap : algebraMap R R = RingHom.id R) (w : HeightOneSpectrum R) :
    heightOneSpectrumContractionOfEtale (R := R) (S := R) w = w := by
  apply HeightOneSpectrum.ext
  rw [heightOneSpectrumContractionOfEtale_asIdeal]
  change Ideal.comap (algebraMap R R) w.asIdeal = w.asIdeal
  rw [hmap]
  rfl

/-- Every height-one contraction fiber is finite, by quasi-finiteness of an
etale algebra. -/
theorem finite_heightOneSpectrumContractionOfEtale_fiber
    (v : HeightOneSpectrum R) :
    {w : HeightOneSpectrum S | heightOneSpectrumContractionOfEtale w = v}.Finite := by
  have hprimes : (v.asIdeal.primesOver S).Finite :=
    Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) v.asIdeal
  apply hprimes.of_injOn
  · intro w hw
    have hcon := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hw
    change w.asIdeal.under R = v.asIdeal at hcon
    change w.asIdeal ∈ v.asIdeal.primesOver S
    exact ⟨w.isPrime, ⟨hcon.symm⟩⟩
  · intro w hw w' hw' heq
    exact IsDedekindDomain.HeightOneSpectrum.ext heq

/-- Pullback of a finite divisor along an affine etale map, defined by
precomposition with the height-one contraction map. -/
noncomputable def affineEtaleDivisorPullback :
    (HeightOneSpectrum R →₀ ℤ) →+ (HeightOneSpectrum S →₀ ℤ) where
  toFun D := by
    classical
    let support := D.support.biUnion (fun v =>
      (finite_heightOneSpectrumContractionOfEtale_fiber (R := R) (S := S) v).toFinset)
    exact Finsupp.mk support
      (fun w => D (heightOneSpectrumContractionOfEtale w)) (by
        intro w
        constructor
        · intro hw
          rcases Finset.mem_biUnion.mp hw with ⟨v, hvD, hvw⟩
          have hcon : heightOneSpectrumContractionOfEtale w = v :=
            (finite_heightOneSpectrumContractionOfEtale_fiber
              (R := R) (S := S) v).mem_toFinset.mp hvw
          rw [hcon]
          exact Finsupp.mem_support_iff.mp hvD
        · intro hw
          apply Finset.mem_biUnion.mpr
          refine ⟨heightOneSpectrumContractionOfEtale w,
            Finsupp.mem_support_iff.mpr hw, ?_⟩
          exact (finite_heightOneSpectrumContractionOfEtale_fiber
            (R := R) (S := S) (heightOneSpectrumContractionOfEtale w)).mem_toFinset.mpr rfl)
  map_zero' := by
    classical
    ext w
    rfl
  map_add' D E := by
    classical
    ext w
    rfl

@[simp] theorem affineEtaleDivisorPullback_apply
    (D : HeightOneSpectrum R →₀ ℤ) (w : HeightOneSpectrum S) :
    affineEtaleDivisorPullback D w =
      D (heightOneSpectrumContractionOfEtale w) := rfl

/-- Pullback along the identity algebra map fixes every finite divisor. -/
theorem affineEtaleDivisorPullback_id
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R R] [Algebra.Etale R R]
    (hmap : algebraMap R R = RingHom.id R)
    (D : HeightOneSpectrum R →₀ ℤ) :
    affineEtaleDivisorPullback (R := R) (S := R) D = D := by
  ext w
  rw [affineEtaleDivisorPullback_apply]
  rw [heightOneSpectrumContractionOfEtale_id (R := R) hmap]

/-- Pullback of finite divisors is contravariantly functorial under
composition of affine etale maps. -/
theorem affineEtaleDivisorPullback_comp
    {T : Type*} [CommRing T] [IsDedekindDomain T]
    [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.Etale S T] [Algebra.Etale R T]
    (D : HeightOneSpectrum R →₀ ℤ) :
    let _hS : IsDedekindDomain S :=
      IsDedekindDomain.of_essFiniteType_formallyUnramified R S
    affineEtaleDivisorPullback (R := S) (S := T)
      (affineEtaleDivisorPullback (R := R) (S := S) D) =
    affineEtaleDivisorPullback (R := R) (S := T) D := by
  intro hS
  have hcontract (w : HeightOneSpectrum T) :
      heightOneSpectrumContractionOfEtale (R := R) (S := S)
        (heightOneSpectrumContractionOfEtale (R := S) (S := T) w) =
      heightOneSpectrumContractionOfEtale (R := R) (S := T) w :=
    heightOneSpectrumContractionOfEtale_comp
      (R := R) (S := S) (T := T) w
  ext w
  rw [affineEtaleDivisorPullback_apply, affineEtaleDivisorPullback_apply,
    hcontract]
  rw [affineEtaleDivisorPullback_apply]

end AffineEtaleDivisorPullback

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- Height-one primes of a non-field Dedekind domain are the actual closed
points of its affine scheme. The non-field hypothesis excludes the zero prime,
which is closed when the ring is a field but is not height one. -/
noncomputable def equivClosedPoints (hR : ¬ IsField R) :
    HeightOneSpectrum R ≃ closedPoints (Spec (CommRingCat.of R)) :=
  (equivMaximalSpectrum hR).trans
    { toFun := fun m => ⟨m.toPrimeSpectrum,
        PrimeSpectrum.isClosed_singleton_iff_isMaximal _ |>.mpr m.isMaximal⟩
      invFun := fun x => ⟨x.1.asIdeal,
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal x.1).mp x.2⟩
      left_inv := by
        intro m
        apply MaximalSpectrum.ext
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        apply PrimeSpectrum.ext
        rfl }

end IsDedekindDomain.HeightOneSpectrum
