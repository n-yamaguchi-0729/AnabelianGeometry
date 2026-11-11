/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.WeightFiltration.FiniteNormalizationKummerEvaluation
public import Nyll.AnabelianGeometry.WeightFiltration.FiniteNormalizationBaseCoefficients
public import Nyll.AnabelianGeometry.WeightFiltration.LocalKummerInertiaDetection
public import Nyll.AnabelianGeometry.WeightFiltration.PlaceLocalValuation
public import Mathlib.Data.Int.GCD

/-!
# Prime-to-characteristic Kummer inertia detection

The original finite tame coordinate evaluates a local Kummer ratio only
after raising it to the wild normalization factor. We retain that factor
and cancel it on the roots of unity of invertible order. Thus the actual
inertia criterion applies in positive characteristic, without asserting
that arbitrary finite extensions have trivial wild ramification.

This supplies the local input needed to recognize proper H¹ inside the
cohomology of the abelian covers used in the geometric-section criterion.
-/

@[expose] public section

noncomputable section

universe u v w t

open AlgebraicCurve SchemeTheory EtaleFundamentalGroups.Inertia
open AnabelianGeometry.WeightFiltration

namespace AnabelianGeometry.FiniteField

private theorem eq_of_coprime_powers
    {R : Type*} [Field R] {x y : R} {n d : ℕ} (hn : 0 < n)
    (hcop : n.Coprime d) (hxn : x ^ n = 1) (hyn : y ^ n = 1)
    (hd : x ^ d = y ^ d) : x = y := by
  have hy : y ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.ne_of_gt hn)] at hyn
    exact zero_ne_one hyn
  apply (div_eq_one_iff_eq hy).mp
  apply (pow_eq_one_iff_of_coprime hcop).mp
  constructor
  · rw [div_pow, hxn, hyn, div_self one_ne_zero]
  · rw [div_pow, hd, div_self (pow_ne_zero d hy)]

section Local

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsSepClosure K L]
  (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]

/-- The actual finite normalization retains the wild factor in its Kummer
residue equation. The prescribed ambient radical is constructed at a finite stage. -/
private theorem exists_finiteNormalization_kummerResidue_with_wild
    (σ : actualNormalizationInertiaGroup A K L Q)
    (n : ℕ) (hn : 0 < n) (a : A) (β : L) (hβ : β ≠ 0)
    (hpow : β ^ n = algebraMap A L a) (δ : A)
    (hδ : algebraMap A L δ =
      galoisAutomorphismRingHom K L (actualNormalizationInertiaElement A K L Q σ) β / β) :
    ∃ (E : FiniteGaloisIntermediateField K L) (m : ℕ),
      n * m = (IsDiscreteValuationRing.addVal A a).toNat *
        (finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A ∧
      normalizationBaseResidue A L Q δ ^ n = 1 ∧
      normalizationBaseResidue A L Q δ ^
          ((finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A /
            actualFiniteStageTameOrder A K L Q E) =
        (((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val).val ^ m := by
  obtain ⟨E, b, hb, hbpow⟩ := exists_finiteNormalization_radical A K L n hn a β hpow
  have : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
    finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  have : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E) :=
    finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  have : IsDiscreteValuationRing
      (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) :=
    localizationAtPrime_isDiscreteValuationRing
      (finiteAbsoluteNormalizationAlgebra A K L E)
      (finiteAbsoluteNormalizationPrime A K L Q E)
      (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)
  let x := algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
    (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) b
  have hxb : finiteNormalizationLocalAmbient A K L Q E x = β :=
    (finiteNormalizationLocalAmbient_algebraMap A K L Q E b).trans hb
  have hx : x ≠ 0 := by
    intro h
    apply hβ
    rw [← hxb, h, map_zero]
  have hxpow : x ^ n = algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
      (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
      (algebraMap A (finiteAbsoluteNormalizationAlgebra A K L E) a) := by
    rw [← hbpow, map_pow]
  have hfixed : actualFiniteInertiaLocalRingHom A K L Q E σ (x ^ n) = x ^ n := by
    rw [hxpow]
    exact finiteNormalizationLocalAction_base A K L Q E σ a
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  have hm := IsDiscreteValuationRing.addVal_def x u hπ m hu
  obtain ⟨d, hd, hπd, _⟩ := actualFiniteTameCoordinate_exists_coefficient A K L Q E σ π hπ
  obtain ⟨c, hc⟩ := localUnitRatio_exists
    (actualFiniteInertiaLocalRingHom A K L Q E σ) π hπ hd.unit
    (by rw [hd.unit_spec]; exact hπd) x hx
  have hcn := localUnitRatio_pow_eq_one
    (actualFiniteInertiaLocalRingHom A K L Q E σ) x hx c hc n hfixed
  have hres := finiteNormalizationTame_unitRatio A K L Q E σ x hx m hm c hc
  have hamb := finiteNormalizationLocalAmbient_unitRatio A K L Q E σ x
    (by rw [hxb]; exact hβ) c hc
  rw [hxb] at hamb
  have hbase := finiteNormalizationLocalResidue_eq_base_of_ambient_eq A K L Q E
    c δ (hamb.trans hδ.symm)
  have hcn' : (c : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) ^ n =
      1 := congrArg Units.val hcn
  have hroot : normalizationBaseResidue A L Q δ ^ n = 1 := by
    simpa only [map_pow, map_one, hbase] using
      congrArg (actualFiniteLocalResidueMap A K L Q E) hcn'
  have ha : a ≠ 0 := by
    intro ha
    have hz : β ^ n = 0 := by rw [hpow, ha, map_zero]
    exact (pow_ne_zero n hβ) hz
  have hv := finiteNormalizationRadical_value_relation A K L Q E a ha x n hxpow
  rw [hm, ENat.toNat_natCast] at hv
  exact ⟨E, m, hv, hroot, by simpa only [hbase] using hres⟩

/-- The actual Kummer residue is the corresponding tame coefficient power
at every invertible exponent, in arbitrary residue characteristic. -/
theorem kummerResidue_eq_tameCoefficient_pow_of_isUnit
    (σ : actualNormalizationInertiaGroup A K L Q)
    (n : ℕ) (hn : 0 < n) (hnA : IsUnit (n : A))
    (a : A) (β : L) (hβ : β ≠ 0) (hpow : β ^ n = algebraMap A L a) (δ : A)
    (hδ : algebraMap A L δ =
      galoisAutomorphismRingHom K L (actualNormalizationInertiaElement A K L Q σ) β / β) :
    normalizationBaseResidue A L Q δ =
      tameCoefficient A K L Q n hnA σ ^ (IsDiscreteValuationRing.addVal A a).toNat := by
  obtain ⟨E, m, hval, hroot, hres⟩ :=
    exists_finiteNormalization_kummerResidue_with_wild A K L Q σ n hn a β hβ hpow δ hδ
  let d := (finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A /
    actualFiniteStageTameOrder A K L Q E
  have harith := actualFiniteStage_tame_arithmetic A K L Q E
  obtain ⟨F, hF⟩ := exists_actualFiniteStageTameOrder_multiple A K L Q n hnA
  let T : FiniteGaloisIntermediateField K L := E ⊔ F
  have hET : actualFiniteStageTameOrder A K L Q E ∣ actualFiniteStageTameOrder A K L Q T :=
    actualFiniteStageTameOrder_dvd_of_le A K L Q E T le_sup_left
  have hnT : n ∣ actualFiniteStageTameOrder A K L Q T :=
    hF.trans (actualFiniteStageTameOrder_dvd_of_le A K L Q F T le_sup_right)
  have hv : n * m = ((IsDiscreteValuationRing.addVal A a).toNat * d) *
      actualFiniteStageTameOrder A K L Q E := by
    rw [hval, Nat.mul_assoc, Nat.div_mul_cancel harith.1]
  have hm := scaledExponent_eq_div_mul hn hET hnT hv
  have hpower : normalizationBaseResidue A L Q δ ^ d =
      (tameCoefficient A K L Q n hnA σ ^ (IsDiscreteValuationRing.addVal A a).toNat) ^ d := by
    rw [actualFiniteTameCoordinate_tower A K L Q E T le_sup_left σ, ← pow_mul, hm] at hres
    rw [tameCoefficient_eq_finite A K L Q n hnA T hnT σ,
      ← pow_mul, ← pow_mul]
    exact hres
  apply eq_of_coprime_powers hn (harith.2 n hnA) hroot _ hpower
  rw [← pow_mul, Nat.mul_comm (IsDiscreteValuationRing.addVal A a).toNat n,
    pow_mul, tameCoefficient_pow_eq_one A K L Q n hnA σ, one_pow]

/-- Actual normalization inertia fixes a radical exactly when the valuation
is divisible by its invertible exponent. -/
theorem normalizationInertia_fixes_radical_iff_dvd_of_isUnit
    (k : Type t) [Field k] [Algebra k A] [Algebra k L] [IsScalarTower k A L]
    (n : ℕ) (hn : 0 < n) (hnA : IsUnit (n : A))
    (hroot : ∃ ζ : k, IsPrimitiveRoot ζ n)
    (a : A) (β : L) (hβ : β ≠ 0) (hpow : β ^ n = algebraMap A L a) :
    (∀ σ : actualNormalizationInertiaGroup A K L Q,
      galoisAutomorphismRingHom K L (actualNormalizationInertiaElement A K L Q σ) β = β) ↔
        n ∣ (IsDiscreteValuationRing.addVal A a).toNat := by
  let ρ : k →+* Q.ResidueField :=
    (normalizationBaseResidue A L Q).comp (algebraMap k A)
  have hiff (σ : actualNormalizationInertiaGroup A K L Q) :
      galoisAutomorphismRingHom K L (actualNormalizationInertiaElement A K L Q σ) β = β ↔
        tameCoefficient A K L Q n hnA σ ^ (IsDiscreteValuationRing.addVal A a).toNat = 1 := by
    let s := galoisAutomorphismRingHom K L (actualNormalizationInertiaElement A K L Q σ)
    have hfixed : s (β ^ n) = β ^ n := by
      rw [hpow]
      exact (AlgEquiv.restrictScalars A (actualNormalizationInertiaElement A K L Q σ)).commutes a
    obtain ⟨δ, hδ⟩ := exists_constant_kummerRatio n (Nat.ne_of_gt hn) hroot s β hβ hfixed
    have hδA : algebraMap A L (algebraMap k A (δ.val : k)) = s β / β := by
      rw [← IsScalarTower.algebraMap_apply k A L]
      exact hδ
    have hf := kummerResidue_eq_tameCoefficient_pow_of_isUnit A K L Q σ n hn hnA
      a β hβ hpow (algebraMap k A (δ.val : k)) hδA
    constructor
    · intro hs
      have hd : (δ.val : k) = 1 := by
        apply (algebraMap k L).injective
        exact hδ.trans (by rw [show s β = β from hs, div_self hβ, map_one])
      rw [← hf, hd, map_one, map_one]
    · intro ht
      have hd : (δ.val : k) = 1 := by
        apply ρ.injective
        exact (hf.trans ht).trans (map_one ρ).symm
      have hr : s β / β = 1 := hδ.symm.trans (by rw [hd, map_one])
      have he := congrArg (fun z : L => z * β) hr
      rw [div_mul_cancel₀ _ hβ, one_mul] at he
      exact he
  rw [← tameCoefficient_pow_trivial_iff_dvd A K L Q n hnA]
  exact ⟨fun h σ => (hiff σ).mp (h σ), fun h σ => (hiff σ).mpr (h σ)⟩

end Local

/-- Original place inertia detects the order of every nonzero rational
function, for an exponent invertible in the constant field. -/
theorem placeInertia_fixes_radical_iff_dvd_of_isUnit
    (k F L : Type*) [Field k] [Field F] [Field L]
    [Algebra k F] [Algebra F L] [IsSepClosure F L]
    (p : Place k F) [Algebra p.toValuationSubring L]
    [IsScalarTower p.toValuationSubring F L]
    [Algebra k L] [IsScalarTower k p.toValuationSubring L]
    (Q : Ideal (normalizationCommAlgCat p.toValuationSubring L)) [Q.IsMaximal]
    (n : ℕ) (hn : 0 < n) (hnk : IsUnit (n : k))
    (hroot : ∃ ζ : k, IsPrimitiveRoot ζ n)
    (f : F) (hf : f ≠ 0) (β : L) (hβ : β ≠ 0)
    (hpow : β ^ n = algebraMap F L f) :
    (∀ σ : actualNormalizationInertiaGroup p.toValuationSubring F L Q,
      galoisAutomorphismRingHom F L
        (actualNormalizationInertiaElement p.toValuationSubring F L Q σ) β = β) ↔
      (n : ℤ) ∣ p.ord f := by
  have hnA : IsUnit (n : p.toValuationSubring) := by
    simpa only [map_natCast] using hnk.map (algebraMap k p.toValuationSubring)
  have integral (a : p.toValuationSubring) (ha : a ≠ 0)
      (b : L) (hb : b ≠ 0) (hpa : b ^ n = algebraMap p.toValuationSubring L a) :
      (∀ σ : actualNormalizationInertiaGroup p.toValuationSubring F L Q,
        galoisAutomorphismRingHom F L
          (actualNormalizationInertiaElement p.toValuationSubring F L Q σ) b = b) ↔
        (n : ℤ) ∣ p.ord (a : F) := by
    rw [place_ord_eq_addVal p a ha, Int.natCast_dvd_natCast]
    exact normalizationInertia_fixes_radical_iff_dvd_of_isUnit
      p.toValuationSubring F L Q k n hn hnA hroot a b hb hpa
  by_cases hfA : f ∈ p.toValuationSubring
  · let a : p.toValuationSubring := ⟨f, hfA⟩
    have ha : a ≠ 0 := by
      intro h
      exact hf (congrArg (fun z : p.toValuationSubring => (z : F)) h)
    have hpa : β ^ n = algebraMap p.toValuationSubring L a :=
      hpow.trans (IsScalarTower.algebraMap_apply p.toValuationSubring F L a).symm
    exact integral a ha β hβ hpa
  · have ho : p.ord f < 0 := lt_of_not_ge
      (fun h => hfA ((p.mem_iff_ord_nonneg hf).mpr h))
    have hi : f⁻¹ ∈ p.toValuationSubring := (p.mem_iff_ord_nonneg (inv_ne_zero hf)).mpr (by
      rw [p.ord_inv]
      exact neg_nonneg.mpr ho.le)
    let a : p.toValuationSubring := ⟨f⁻¹, hi⟩
    have ha : a ≠ 0 := by
      intro h
      exact (inv_ne_zero hf) (congrArg (fun z : p.toValuationSubring => (z : F)) h)
    have hpa : (β⁻¹) ^ n = algebraMap p.toValuationSubring L a := by
      rw [inv_pow, hpow, ← map_inv₀]
      exact (IsScalarTower.algebraMap_apply p.toValuationSubring F L a).symm
    have h := integral a ha β⁻¹ (inv_ne_zero hβ) hpa
    simpa only [a, map_inv₀, inv_inj, p.ord_inv, dvd_neg] using h

end AnabelianGeometry.FiniteField
