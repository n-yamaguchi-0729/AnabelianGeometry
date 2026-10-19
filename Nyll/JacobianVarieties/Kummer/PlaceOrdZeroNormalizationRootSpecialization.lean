/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.PlaceOrdZeroKummerCover
import Nyll.JacobianVarieties.Kummer.KummerUnitRootSpecialization
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrime
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeField

/-!
# Order-zero Kummer roots in the original normalization localization

The original place supplies its literal valuation ring, and the prescribed
normalization prime supplies its literal localization in the same ambient
field. Existing normalization theorems prove the normal, Henselian, and
fraction-field instances needed for actual finite etale point specialization.
The base remains the original valuation ring throughout.
-/

noncomputable section

open EtaleFundamentalGroups EtaleFundamentalGroups.StrictHenselian

namespace AlgebraicCurve.Place

variable {k F : Type} [Field k] [Field F] [Algebra k F]

/-- The original generic roots specialize to roots of the residue of the
unchanged order-zero unit. The displayed evaluation is through the actual
localization inclusion, rather than an abstract residue-field comparison.
No lying-over or Galois assumption is needed for this root specialization. -/
theorem exists_ordZero_normalizationRootSpecialization
    (v : Place k F) (u : Fˣ) (hu : v.ord (u : F) = 0)
    (n : ℕ) (hn : IsUnit (n : k))
    (Ω : Type) [Field Ω] [Algebra F Ω]
    [Algebra v.toValuationSubring Ω] [IsScalarTower v.toValuationSubring F Ω]
    [Algebra.IsAlgebraic F Ω] [IsSepClosed Ω]
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [Q.IsPrime] :
    ∃ e : {b : Ω // b ^ n = algebraMap F Ω (u : F)} ≃
        {b : IsLocalRing.ResidueField (Localization.AtPrime Q) //
          b ^ n = IsLocalRing.residue (Localization.AtPrime Q)
            (integralClosurePrimeBaseMap v.toValuationSubring Ω Q
              (ordZeroUnit v u hu : v.toValuationSubring))},
      ∀ b, ∃ r : Localization.AtPrime Q,
        integralClosurePrimeToAmbientField v.toValuationSubring F Ω Q r = b.val ∧
          (e b).val = IsLocalRing.residue (Localization.AtPrime Q) r := by
  let a : v.toValuationSubringˣ := ordZeroUnit v u hu
  have : IsFractionRing (integralClosure v.toValuationSubring Ω) Ω :=
    integralClosure_isFractionRing_of_fractionField_algebraic v.toValuationSubring F Ω
  have : IsIntegrallyClosed (integralClosure v.toValuationSubring Ω) :=
    IsIntegrallyClosed.of_isIntegrallyClosedIn (integralClosure v.toValuationSubring Ω) Ω
  have : IsIntegrallyClosed (Localization.AtPrime Q) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime Q)
      Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  have : HenselianLocalRing (Localization.AtPrime Q) :=
    (integralClosure_localizationAtPrime_strictHenselian v.toValuationSubring F Ω Q).1
  let : Algebra (Localization.AtPrime Q) Ω :=
    (integralClosurePrimeToAmbientField v.toValuationSubring F Ω Q).toAlgebra
  have : IsScalarTower (integralClosure v.toValuationSubring Ω)
      (Localization.AtPrime Q) Ω :=
    IsScalarTower.of_algebraMap_eq'
      (integralClosurePrimeToAmbientField_comp_coefficient v.toValuationSubring F Ω Q).symm
  have : IsFractionRing (Localization.AtPrime Q) Ω :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      Q.primeCompl (Localization.AtPrime Q) Ω
  have hbase : algebraMap v.toValuationSubring (Localization.AtPrime Q) =
      integralClosurePrimeBaseMap v.toValuationSubring Ω Q :=
    IsScalarTower.algebraMap_eq v.toValuationSubring
      (integralClosure v.toValuationSubring Ω) (Localization.AtPrime Q)
  have : IsScalarTower v.toValuationSubring (Localization.AtPrime Q) Ω := by
    apply IsScalarTower.of_algebraMap_eq' (R := v.toValuationSubring)
      (S := Localization.AtPrime Q) (A := Ω)
    rw [hbase]
    exact (integralClosurePrimeToAmbientField_comp_baseMap v.toValuationSubring F Ω Q).symm
  have hnA : IsUnit (n : v.toValuationSubring) := by
    simpa only [map_natCast] using hn.map (algebraMap k v.toValuationSubring)
  have hcoeff : algebraMap v.toValuationSubring Ω (a : v.toValuationSubring) =
      algebraMap F Ω (u : F) := by
    rw [IsScalarTower.algebraMap_eq v.toValuationSubring F Ω]
    rfl
  let eGeneric : {b : Ω // b ^ n = algebraMap F Ω (u : F)} ≃
      {b : Ω // b ^ n = algebraMap v.toValuationSubring Ω (a : v.toValuationSubring)} := {
    toFun := fun b => ⟨b.val, b.property.trans hcoeff.symm⟩
    invFun := fun b => ⟨b.val, b.property.trans hcoeff⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hres : algebraMap v.toValuationSubring
        (IsLocalRing.ResidueField (Localization.AtPrime Q)) (a : v.toValuationSubring) =
      IsLocalRing.residue (Localization.AtPrime Q)
        (integralClosurePrimeBaseMap v.toValuationSubring Ω Q (a : v.toValuationSubring)) := by
    change IsLocalRing.residue (Localization.AtPrime Q)
        (algebraMap v.toValuationSubring (Localization.AtPrime Q) (a : v.toValuationSubring)) =
      IsLocalRing.residue (Localization.AtPrime Q)
        (integralClosurePrimeBaseMap v.toValuationSubring Ω Q (a : v.toValuationSubring))
    exact congrArg (IsLocalRing.residue (Localization.AtPrime Q))
      (RingHom.congr_fun hbase (a : v.toValuationSubring))
  let eResidue :
      {b : IsLocalRing.ResidueField (Localization.AtPrime Q) //
        b ^ n = algebraMap v.toValuationSubring
          (IsLocalRing.ResidueField (Localization.AtPrime Q)) (a : v.toValuationSubring)} ≃
      {b : IsLocalRing.ResidueField (Localization.AtPrime Q) // b ^ n =
        IsLocalRing.residue (Localization.AtPrime Q)
          (integralClosurePrimeBaseMap v.toValuationSubring Ω Q (a : v.toValuationSubring))} := {
    toFun := fun b => ⟨b.val, b.property.trans hres⟩
    invFun := fun b => ⟨b.val, b.property.trans hres.symm⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let e := eGeneric.trans
    ((SchemeTheory.kummerUnitRootSpecialization v.toValuationSubring
      (Localization.AtPrime Q) Ω n a hnA).trans eResidue)
  refine ⟨e, ?_⟩
  intro b
  obtain ⟨r, hr, hresidue⟩ :=
    SchemeTheory.kummerUnitRootSpecialization_evaluation v.toValuationSubring
      (Localization.AtPrime Q) Ω n a hnA (eGeneric b)
  exact ⟨r, hr, hresidue⟩

end AlgebraicCurve.Place
