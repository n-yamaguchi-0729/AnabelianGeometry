/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.TorsionIntegralReduction
import Nyll.ProCGroups.Abelian.RestrictedTateTransport
import Nyll.AnabelianGeometry.WeightFiltration.FrobeniusFixedTate

/-!
# Continuous specialization of actual restricted Tate modules

The finite-level additive specialization respects the original multiplication
transitions, so it transports the existing restricted Tate module and topology.
Every index is required to be a unit in the given local base model.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry ProCGroups

namespace GoodReductionJacobian.RelativeGroupLaw

variable {H : Type} [CommRing H] {A : Scheme} {f : A ⟶ Spec (.of H)}
  (G : RelativeGroupLaw H f) (hc : G.IsCommutative)

/-- Actual coefficient extension on the existing restricted Tate module. -/
def restrictedTateCoefficientMap
    {T T' : Type} [CommRing T] [CommRing T'] [Algebra H T] [Algebra H T']
    (a : T →ₐ[H] T') (I : Submonoid ℕ+) :
    Multiplicative (RestrictedTateModule (G.AlgPoints hc T) I) →ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc T') I) :=
  RestrictedTateModule.mapLevelsHom (fun n => G.torsionCoefficientMap hc a n.1)
    (fun n m x => G.torsionCoefficientMap_transition hc a n.1 m.1 x)

variable [IsLocalRing H] [IsProper f] [Smooth f]
  (R L : Type) [CommRing R] [HenselianLocalRing R] [IsIntegrallyClosed R]
  [Field L] [Algebra H R] [Algebra R L] [IsFractionRing R L]
  [Algebra H L] [IsScalarTower H R L]

/-- Actual specialization is a continuous equivalence at every allowed unit index. -/
def restrictedTateSpecialization
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : H)) :
    Multiplicative (RestrictedTateModule (G.AlgPoints hc L) I) ≃ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc (IsLocalRing.ResidueField R)) I) :=
  RestrictedTateModule.equivLevels
    (fun n => G.torsionSpecializationAddEquiv hc R L n.1 (hI n))
    (fun n m x => G.torsionSpecializationAddEquiv_transition hc R L
      n.1 m.1 (hI n) (hI (n * m)) x)

/-- The continuous comparison is the actual specialization at every torsion level. -/
@[simp] theorem restrictedTateSpecialization_projection
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : H))
    (x : Multiplicative (RestrictedTateModule (G.AlgPoints hc L) I)) (n : I) :
    RestrictedTateModule.projection (G.AlgPoints hc (IsLocalRing.ResidueField R)) I n
        (Multiplicative.toAdd (G.restrictedTateSpecialization hc R L I hI x)) =
      G.torsionSpecializationAddEquiv hc R L n.1 (hI n)
        (RestrictedTateModule.projection (G.AlgPoints hc L) I n
          (Multiplicative.toAdd x)) := rfl

/-- The continuous specialization intertwines the actual compatible coefficient actions. -/
theorem restrictedTateSpecialization_equivariant
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : H))
    (τ : R ≃ₐ[H] R) (σ : L ≃ₐ[H] L)
    (hσ : ∀ r : R, σ (algebraMap R L r) = algebraMap R L (τ r))
    (x : Multiplicative (RestrictedTateModule (G.AlgPoints hc L) I)) :
    G.restrictedTateSpecialization hc R L I hI
        (G.restrictedTateCoefficientMap hc σ.toAlgHom I x) =
      G.restrictedTateCoefficientMap hc (SchemeTheory.residueAlgEquiv H R τ).toAlgHom I
        (G.restrictedTateSpecialization hc R L I hI x) := by
  apply Multiplicative.toAdd.injective
  apply RestrictedTateModule.ext
  intro n
  exact congrArg Subtype.val (G.torsionSpecializationAddEquiv_equivariant hc R L τ σ hσ
    n.1 (hI n) (RestrictedTateModule.projection (G.AlgPoints hc L) I n
      (Multiplicative.toAdd x)))

/-- Fixed vectors vanish on the original generic fibre if the induced residue
coefficient action has finitely many fixed values. All coordinates use the same model. -/
theorem restrictedTate_eq_one_of_specialization_fixed_values
    [CompactSpace A] (I : Submonoid ℕ+)
    (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : H))
    (τ : R ≃ₐ[H] R) (σ : L ≃ₐ[H] L)
    [Finite {z : IsLocalRing.ResidueField R // SchemeTheory.residueAlgEquiv H R τ z = z}]
    (hσ : ∀ r : R, σ (algebraMap R L r) = algebraMap R L (τ r))
    (x : Multiplicative (RestrictedTateModule (G.AlgPoints hc L) I))
    (hx : G.restrictedTateCoefficientMap hc σ.toAlgHom I x = x) : x = 1 := by
  let e := G.restrictedTateSpecialization hc R L I hI
  have hfix : G.restrictedTateCoefficientMap hc
      (SchemeTheory.residueAlgEquiv H R τ).toAlgHom I (e x) = e x := by
    rw [← G.restrictedTateSpecialization_equivariant hc R L I hI τ σ hσ, hx]
  have hz : Multiplicative.toAdd (e x) = 0 := by
    apply AnabelianGeometry.WeightFiltration.restrictedTate_eq_zero_of_fixed
      H (IsLocalRing.ResidueField R) A f G hc (SchemeTheory.residueAlgEquiv H R τ)
      I (Multiplicative.toAdd (e x))
    intro n
    exact congrArg (fun y => RestrictedTateModule.evaluation
      (G.AlgPoints hc (IsLocalRing.ResidueField R)) I n (Multiplicative.toAdd y)) hfix
  apply e.injective
  rw [map_one]
  exact congrArg Multiplicative.ofAdd hz

end GoodReductionJacobian.RelativeGroupLaw
