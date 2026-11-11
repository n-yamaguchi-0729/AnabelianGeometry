/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence
public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationAbsoluteResidueGroup
public import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationResidueAction
public import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationSpecializationResidueAction
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Frobenius in the original decomposition group of a normal local domain

Finite base residue supplies an actual residue Frobenius. The proved original
normalization residue surjection lifts it to the original Galois group. Its
action on every finite étale algebra over the ordinary henselization is the
same residue power under the already constructed specialization equivalence.
No discrete valuation or proper-family comparison is required.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- A finite-residue normal local domain supplies a single actual decomposition
element acting by arithmetic Frobenius on the whole normalization residue. -/
theorem exists_normalization_frobenius_of_finite_residue
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Finite (IsLocalRing.ResidueField A)]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal] :
    ∃ d : (normalizationDecompositionGroup A K L Q).carrier,
      (∀ z : (normalizationResidueFieldObject A L Q).α,
        actualNormalizationQuotientActionScalar A K L Q d z =
          z ^ Nat.card (IsLocalRing.ResidueField A)) ∧
      ∀ z : Q.ResidueField,
        actualNormalizationResidueFieldMap A K L Q d z =
          z ^ Nat.card (IsLocalRing.ResidueField A) := by
  let k := IsLocalRing.ResidueField A
  let E := normalizationResidueFieldObject A L Q
  let : Fintype k := Fintype.ofFinite k
  let aE : Algebra k E.α := normalizationResidueFieldAlgebra A L Q
  have : Algebra.IsAlgebraic k E.α := normalizationResidueFieldAlgebra_isAlgebraic A L Q
  let Φ : E.α ≃ₐ[k] E.α := FiniteField.frobeniusAlgEquivOfAlgebraic k E.α
  let e := eqToIso (normalizationResidueAutomorphisms_eq_fieldObject A L Q)
  let ρ : (normalizationResidueAutomorphisms A L Q).carrier := e.inv.hom' Φ
  obtain ⟨d, hd⟩ := normalizationResidueMorphism_surjective A K L Q ρ
  have he : e.hom.hom' ρ = Φ := ConcreteCategory.congr_hom e.inv_hom_id Φ
  have hpower (z : E.α) :
      normalizationResidueActionScalar A L Q ρ z = z ^ Nat.card k := by
    calc
      normalizationResidueActionScalar A L Q ρ z =
          nativeFieldResidueActionScalar k E aE (e.hom.hom' ρ) z :=
        (normalizationResidueAutomorphisms_fieldObject_apply A L Q ρ z).symm
      _ = nativeFieldResidueActionScalar k E aE Φ z :=
        congrArg (fun σ => nativeFieldResidueActionScalar k E aE σ z) he
      _ = z ^ Nat.card k := by
        change Φ z = z ^ Nat.card k
        rw [Nat.card_eq_fintype_card]
        exact congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic k E.α) z
  have hquot (z : E.α) :
      actualNormalizationQuotientActionScalar A K L Q d z = z ^ Nat.card k := by
    change normalizationResidueActionScalar A L Q
      ((normalizationResidueMorphism A K L Q).hom' d) z = _
    exact (congrArg (fun r => normalizationResidueActionScalar A L Q r z) hd).trans
      (hpower z)
  refine ⟨d, hquot, ?_⟩
  intro z
  let eQ := maximalQuotientResidueEquiv Q
  change eQ (actualNormalizationQuotientActionScalar A K L Q d (eQ.symm z)) = _
  calc
    _ = eQ ((eQ.symm z) ^ Nat.card k) := congrArg eQ (hquot (eQ.symm z))
    _ = z ^ Nat.card k := by rw [map_pow, eQ.apply_symm_apply]

end EtaleFundamentalGroups.Inertia

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia SchemeTheory

universe u v

attribute [local instance] normalizationInertiaImageAction

/-- The same constructed original Frobenius acts by the residue-cardinality
power on all specialized finite étale points, simultaneously at every level. -/
theorem exists_normalization_frobenius_finiteEtale_points
    (A : Type u) (K : Type v) (L : Type u)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Finite (IsLocalRing.ResidueField A)]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
    (Q : Ideal (integralClosure A L)) [hQmax : Q.IsMaximal]
    (hQ : Q.under A = IsLocalRing.maximalIdeal A) :
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    let nativeQ : Ideal (normalizationCommAlgCat A L).carrier := Q
    let : nativeQ.IsMaximal := hQmax
    ∃ d : (normalizationDecompositionGroup A K L nativeQ).carrier,
      (∀ z : Q.ResidueField,
        actualNormalizationResidueFieldMap A K L nativeQ d z =
          z ^ Nat.card (IsLocalRing.ResidueField A)) ∧
      ∀ (T : Type u) [CommRing T] [Algebra (ordinaryHenselization A) T]
        [Module.Finite (ordinaryHenselization A) T]
        [Algebra.Etale (ordinaryHenselization A) T]
        (f : T →ₐ[ordinaryHenselization A] L) (x : T),
        normalizationFiniteEtalePointSpecialization A K L Q hQ T
            ((normalizationDecompositionFieldHenselizationAlgEquiv
              A K L Q hQ d).toAlgHom.comp f) x =
          (normalizationFiniteEtalePointSpecialization A K L Q hQ T f x) ^
            Nat.card (IsLocalRing.ResidueField A) := by
  intro actualLocalAlgebra actualAmbientAlgebra nativeQ nativeMaximal
  obtain ⟨d, _, hd⟩ := exists_normalization_frobenius_of_finite_residue A K L nativeQ
  refine ⟨d, hd, ?_⟩
  intro T actualRing actualAlgebra actualFinite actualEtale f x
  have hspec := normalizationFiniteEtalePointSpecialization_equivariant A K L Q hQ T d f
  have hvalue := congrArg (fun g : T →ₐ[ordinaryHenselization A]
    IsLocalRing.ResidueField (Localization.AtPrime Q) => g x) hspec
  have haction := normalizationSpecializationResidueAction_eq A K L Q hQ d
  exact hvalue.trans ((RingHom.congr_fun haction
    (normalizationFiniteEtalePointSpecialization A K L Q hQ T f x)).trans (hd _))

end EtaleFundamentalGroups.StrictHenselian
