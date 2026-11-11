/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.NormalLocalFrobeniusLift
public import Nyll.SchemeTheory.RingTheory.Henselian.NormalLocalResiduePowerRoots
public import Mathlib.FieldTheory.Finite.Basic
public import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeField
public import Nyll.SchemeTheory.FiniteEtale.Algebra.PointSpecialization

/-!
# Actual normal-local Frobenius data for Picard weight separation

The local target is the localization of the actual integral closure in the
original separably closed Galois field. Its existing strict Henselianity,
normality, fraction map, and original decomposition action supply all the
local automorphisms, coefficient equations, fixed-value finiteness, and
roots formulas needed by the Picard specialization theorem.
-/

@[expose] public section

noncomputable section

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia SchemeTheory

universe u v

attribute [local instance] normalizationInertiaImageAction

/-- The literal normalization localization supplies Frobenius automorphisms
with all local-ring and roots data required for Tate weight separation. -/
theorem exists_normalization_frobenius_data
    (A : Type u) (K : Type v) (L : Type u)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Finite (IsLocalRing.ResidueField A)]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
    (Q : Ideal (integralClosure A L)) [hQmax : Q.IsMaximal] :
    let R := Localization.AtPrime Q
    let : Algebra R L := (integralClosurePrimeToAmbientField A K L Q).toAlgebra
    HenselianLocalRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R L ∧
      IsScalarTower A R L ∧
      ∃ (σ : Gal(L/K)) (τ : R ≃ₐ[A] R),
        (∀ r : R, σ (algebraMap R L r) = algebraMap R L (τ r)) ∧
        (∀ z : IsLocalRing.ResidueField R,
          SchemeTheory.residueAlgEquiv A R τ z = z ^ Nat.card (IsLocalRing.ResidueField A)) ∧
        Finite {z : IsLocalRing.ResidueField R // SchemeTheory.residueAlgEquiv A R τ z = z} ∧
        ∀ (n : ℕ), IsUnit (n : A) → ∀ x : L, x ^ n = 1 →
          σ x = x ^ Nat.card (IsLocalRing.ResidueField A) := by
  intro R actualAmbientAlgebra
  let B := integralClosure A L
  have : IsFractionRing B L := integralClosure_isFractionRing_of_fractionField_algebraic A K L
  have : IsIntegrallyClosed B := IsIntegrallyClosed.of_isIntegrallyClosedIn B L
  have : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isLocalization R Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  have : HenselianLocalRing R :=
    (integralClosure_localizationAtPrime_strictHenselian A K L Q).1
  have : IsScalarTower B R L := IsScalarTower.of_algebraMap_eq'
    (integralClosurePrimeToAmbientField_comp_coefficient A K L Q).symm
  have : IsFractionRing R L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl R L
  have : IsScalarTower A R L := IsScalarTower.of_algebraMap_eq'
    (integralClosurePrimeToAmbientField_comp_baseMap A K L Q).symm
  let nativeQ : Ideal (normalizationCommAlgCat A L).carrier := Q
  have : nativeQ.IsMaximal := hQmax
  obtain ⟨d, _, hd⟩ := exists_normalization_frobenius_of_finite_residue A K L nativeQ
  let τ : R ≃ₐ[A] R :=
    { stabilizerLocalizationRingEquiv B Gal(L/K) Q d with
      commutes' := by
        intro a
        change stabilizerLocalizationRingEquiv B Gal(L/K) Q d
          (algebraMap B R (algebraMap A B a)) = algebraMap B R (algebraMap A B a)
        exact (stabilizerLocalizationRingEquiv_algebraMap B Gal(L/K) Q d
          (algebraMap A B a)).trans (congrArg (algebraMap B R)
          (RingHom.congr_fun (normalizationCommAlg_action_comp_coefficient A K L d.val) a)) }
  have hcompat (r : R) : d.val (algebraMap R L r) = algebraMap R L (τ r) :=
    RingHom.congr_fun (integralClosurePrimeToAmbientField_comp_decomposition A K L Q d) r
  have hQ : Q.under A = IsLocalRing.maximalIdeal A :=
    integralClosure_maximalPrime_under A L Q
  have haction : (SchemeTheory.residueAlgEquiv A R τ).toRingHom =
      actualNormalizationResidueFieldMap A K L nativeQ d :=
    normalizationSpecializationResidueAction_eq A K L Q hQ d
  have hres (z : IsLocalRing.ResidueField R) :
      SchemeTheory.residueAlgEquiv A R τ z = z ^ Nat.card (IsLocalRing.ResidueField A) :=
    (RingHom.congr_fun haction z).trans (hd z)
  let q := Nat.card (IsLocalRing.ResidueField A)
  have hfinite :
      Finite {z : IsLocalRing.ResidueField R // SchemeTheory.residueAlgEquiv A R τ z = z} := by
    let : Fintype (IsLocalRing.ResidueField A) := Fintype.ofFinite _
    have hq : 1 < q := by
      change 1 < Nat.card (IsLocalRing.ResidueField A)
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have hset : {z : IsLocalRing.ResidueField R | SchemeTheory.residueAlgEquiv A R τ z = z} =
        {z | Polynomial.IsRoot
          (Polynomial.X ^ q - Polynomial.X : Polynomial (IsLocalRing.ResidueField R)) z} := by
      ext z
      change (SchemeTheory.residueAlgEquiv A R τ z = z) ↔ _
      rw [hres]
      simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, sub_eq_zero, Set.mem_ofPred_eq, q]
    have hfin : Set.Finite
        {z : IsLocalRing.ResidueField R | SchemeTheory.residueAlgEquiv A R τ z = z} := by
      rw [hset]
      exact Polynomial.finite_setOfPred_isRoot
        (FiniteField.X_pow_card_sub_X_ne_zero (IsLocalRing.ResidueField R) hq)
    exact hfin.to_subtype
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, d.val, τ,
    hcompat, hres, hfinite, ?_⟩
  intro n hn x hx
  have hnR : IsUnit (n : R) := by
    simpa only [map_natCast] using hn.map (algebraMap A R)
  apply SchemeTheory.cyclotomic_power_of_residue_power_of_normal_local R L
    τ.toRingEquiv d.val.toRingEquiv hcompat q ?_ n hnR x hx
  intro r
  exact (SchemeTheory.residueAlgEquiv_residue A R τ r).symm.trans
    (hres (IsLocalRing.residue R r))

end EtaleFundamentalGroups.StrictHenselian
