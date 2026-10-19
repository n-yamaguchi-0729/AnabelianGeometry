/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.PlaceOrdZeroNormalizationRootSpecialization
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeOrdinaryHenselization
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationResidueAction
import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction

/-!
# Original decomposition action on the same specialized Kummer roots

The existing specialization and its integral-lift evaluation are retained.
The prescribed localization inclusion intertwines the original decomposition
automorphism with its literal localization automorphism. Injectivity then
identifies the two integral lifts, and actual residue reduction gives the
original normalization residue action. No compatible-actions hypothesis or
replacement root equivalence is introduced.
-/

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia EtaleFundamentalGroups.StrictHenselian
open scoped Pointwise

namespace AlgebraicCurve.Place

attribute [local instance] normalizationInertiaImageAction normalizationCommAlgGaloisAction

private theorem actualNormalizationResidueFieldMap_residue
    (A F Ω : Type) [CommRing A] [Field F] [Field Ω]
    [Algebra A F] [IsFractionRing A F] [Algebra F Ω] [Algebra A Ω]
    [IsScalarTower A F Ω] [IsGalois F Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
    (d : (normalizationDecompositionGroup A F Ω Q).carrier)
    (r : Localization.AtPrime Q) :
    actualNormalizationResidueFieldMap A F Ω Q d
        (IsLocalRing.residue (Localization.AtPrime Q) r) =
      IsLocalRing.residue (Localization.AtPrime Q)
        (stabilizerLocalizationRingEquiv (normalizationCommAlgCat A Ω) Gal(Ω/F) Q d r) := by
  let τ : Localization.AtPrime Q ≃+* Localization.AtPrime Q :=
    stabilizerLocalizationRingEquiv (normalizationCommAlgCat A Ω) Gal(Ω/F) Q d
  have : IsLocalHom τ.toRingHom :=
    isLocalHom_of_leftInverse τ.symm.toRingHom (fun x => τ.symm_apply_apply x)
  let ρ : IsLocalRing.ResidueField (Localization.AtPrime Q) ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime Q) :=
    IsLocalRing.ResidueField.mapEquiv τ
  have hcoeff (b : normalizationCommAlgCat A Ω) :
      algebraMap (normalizationCommAlgCat A Ω)
          (IsLocalRing.ResidueField (Localization.AtPrime Q)) b =
        IsLocalRing.residue (Localization.AtPrime Q)
          (algebraMap (normalizationCommAlgCat A Ω) (Localization.AtPrime Q) b) :=
    rfl
  have hmap : ρ.toRingHom = actualNormalizationResidueFieldMap A F Ω Q d := by
    apply RingHom.ext
    intro z
    obtain ⟨b, rfl⟩ := Q.algebraMap_residueField_surjective z
    calc
      ρ (algebraMap (normalizationCommAlgCat A Ω) Q.ResidueField b) =
          ρ (IsLocalRing.residue (Localization.AtPrime Q)
            (algebraMap (normalizationCommAlgCat A Ω) (Localization.AtPrime Q) b)) :=
        congrArg ρ (hcoeff b)
      _ = IsLocalRing.residue (Localization.AtPrime Q)
          (τ (algebraMap (normalizationCommAlgCat A Ω) (Localization.AtPrime Q) b)) :=
        IsLocalRing.ResidueField.map_residue τ.toRingHom _
      _ = IsLocalRing.residue (Localization.AtPrime Q)
          (algebraMap (normalizationCommAlgCat A Ω) (Localization.AtPrime Q) (d.val • b)) :=
        congrArg (IsLocalRing.residue (Localization.AtPrime Q))
          (stabilizerLocalizationRingEquiv_algebraMap
            (normalizationCommAlgCat A Ω) Gal(Ω/F) Q d b)
      _ = algebraMap (normalizationCommAlgCat A Ω) Q.ResidueField (d.val • b) :=
        (hcoeff _).symm
      _ = algebraMap (normalizationCommAlgCat A Ω) Q.ResidueField
          (normalizationGaloisRingHom A F Ω d.val b) :=
        congrArg (algebraMap (normalizationCommAlgCat A Ω) Q.ResidueField)
          (RingHom.congr_fun (normalizationGaloisRingHom_eq_original A F Ω d.val) b).symm
      _ = actualNormalizationResidueFieldMap A F Ω Q d
          (algebraMap (normalizationCommAlgCat A Ω) Q.ResidueField b) :=
        (actualNormalizationResidueFieldMap_coefficient A F Ω Q d b).symm
  rw [← hmap]
  exact IsLocalRing.ResidueField.map_residue τ.toRingHom r

variable {k F : Type} [Field k] [Field F] [Algebra k F]

/-- The same actual root specialization retains its literal integral-lift
evaluation and intertwines every original decomposition element with the
original normalization residue action. -/
theorem exists_ordZero_normalizationRootSpecialization_equivariant
    (v : Place k F) (u : Fˣ) (hu : v.ord (u : F) = 0)
    (n : ℕ) (hn : IsUnit (n : k))
    (Ω : Type) [Field Ω] [Algebra F Ω]
    [Algebra v.toValuationSubring Ω] [IsScalarTower v.toValuationSubring F Ω]
    [IsGalois F Ω] [IsSepClosed Ω]
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [hQmax : Q.IsMaximal] :
    let nativeQ : Ideal (normalizationCommAlgCat v.toValuationSubring Ω) := Q
    letI : nativeQ.IsMaximal := hQmax
    ∃ e : {b : Ω // b ^ n = algebraMap F Ω (u : F)} ≃
        {b : IsLocalRing.ResidueField (Localization.AtPrime Q) //
          b ^ n = IsLocalRing.residue (Localization.AtPrime Q)
            (integralClosurePrimeBaseMap v.toValuationSubring Ω Q
              (ordZeroUnit v u hu : v.toValuationSubring))},
      (∀ b, ∃ r : Localization.AtPrime Q,
        integralClosurePrimeToAmbientField v.toValuationSubring F Ω Q r = b.val ∧
          (e b).val = IsLocalRing.residue (Localization.AtPrime Q) r) ∧
      ∀ (d : (normalizationDecompositionGroup v.toValuationSubring F Ω nativeQ).carrier)
        (b : {b : Ω // b ^ n = algebraMap F Ω (u : F)}),
        (e ⟨d.val b.val, by rw [← map_pow, b.property, d.val.commutes]⟩).val =
          actualNormalizationResidueFieldMap v.toValuationSubring F Ω nativeQ d (e b).val := by
  intro nativeQ
  let : nativeQ.IsMaximal := hQmax
  let : MulSemiringAction Gal(Ω/F) (integralClosure v.toValuationSubring Ω) :=
    normalizationInertiaImageAction v.toValuationSubring F Ω
  obtain ⟨e, he⟩ := exists_ordZero_normalizationRootSpecialization v u hu n hn Ω Q
  refine ⟨e, he, ?_⟩
  intro d b
  let dRaw : MulAction.stabilizer Gal(Ω/F) Q := d
  let b' : {b : Ω // b ^ n = algebraMap F Ω (u : F)} :=
    ⟨d.val b.val, by rw [← map_pow, b.property, d.val.commutes]⟩
  obtain ⟨r, hr, hresidue⟩ := he b
  obtain ⟨r', hr', hresidue'⟩ := he b'
  let τ : Localization.AtPrime Q ≃+* Localization.AtPrime Q :=
    stabilizerLocalizationRingEquiv
      (integralClosure v.toValuationSubring Ω) Gal(Ω/F) Q dRaw
  have hlift : r' = τ r := by
    apply integralClosurePrimeToAmbientField_injective v.toValuationSubring F Ω Q
    exact hr'.trans ((congrArg d.val hr.symm).trans
      (RingHom.congr_fun
        (integralClosurePrimeToAmbientField_comp_decomposition
          v.toValuationSubring F Ω Q dRaw) r))
  change (e b').val =
    actualNormalizationResidueFieldMap v.toValuationSubring F Ω nativeQ d (e b).val
  rw [hresidue', hlift, hresidue]
  exact (actualNormalizationResidueFieldMap_residue v.toValuationSubring F Ω nativeQ d r).symm

end AlgebraicCurve.Place
