/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.PlaceOrdZeroNormalizationRootAction
import Nyll.JacobianVarieties.Kummer.PlaceOrdZeroRationalRootScaling

/-!
# One rational root specialization with scaling and original decomposition action

Keep the equivalence already supplied with full constant-root scaling. Its
literal lift evaluation identifies it with the normalization specialization,
by injectivity of the prescribed ambient inclusion. The canonical constant
residue map intertwines the original residue action with restriction to the
fixed constants, as proved on actual normalization coefficients.

The action label here is the literal fixed-field restriction of the original
decomposition element. This file does not identify that label with the
arithmetic fundamental-group projection: the latter's fixed inner-conjugacy
correction remains to be handled at the arithmetic caller.
-/

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia EtaleFundamentalGroups.StrictHenselian

namespace AlgebraicCurve.Place

attribute [local instance] normalizationInertiaImageAction normalizationCommAlgGaloisAction

private theorem canonicalConstantResidueMap_equivariant
    (k A F κ Ω : Type) [Field k] [CommRing A] [IsLocalRing A]
    [Field F] [Field κ] [Field Ω]
    [Algebra k A] [Algebra k F] [Algebra k κ] [Algebra k Ω]
    [Algebra A F] [IsFractionRing A F] [Algebra F Ω] [Algebra A Ω] [Algebra κ Ω]
    [IsScalarTower A F Ω] [IsScalarTower k A Ω]
    [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
    [Normal k κ] [IsGalois F Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
    (d : (normalizationDecompositionGroup A F Ω Q).carrier) (x : κ) :
    let c : κ →+* IsLocalRing.ResidueField (Localization.AtPrime Q) :=
      (maximalQuotientResidueEquiv Q).toRingHom.comp
        (arithmeticConstantResidueMap k A κ Ω Q)
    actualNormalizationResidueFieldMap A F Ω Q d (c x) =
      c (((d.val.restrictScalars k).restrictNormal κ) x) := by
  intro c
  let δ : κ ≃ₐ[k] κ := (d.val.restrictScalars k).restrictNormal κ
  have hcoeff (z : κ) : c z =
      algebraMap (normalizationCommAlgCat A Ω) Q.ResidueField
        (arithmeticConstantNormalizationMap k A κ Ω z) :=
    RingHom.congr_fun (maximalQuotientResidueEquiv_comp_quotient Q)
      (arithmeticConstantNormalizationMap k A κ Ω z)
  have hconstant :
      normalizationGaloisRingHom A F Ω d.val
          (arithmeticConstantNormalizationMap k A κ Ω x) =
        arithmeticConstantNormalizationMap k A κ Ω (δ x) := by
    apply Subtype.ext
    exact (RingHom.congr_fun (normalizationGaloisRingHom_commutes A F Ω d.val)
      (arithmeticConstantNormalizationMap k A κ Ω x)).trans
        ((d.val.restrictScalars k).restrictNormal_commutes κ x).symm
  calc
    actualNormalizationResidueFieldMap A F Ω Q d (c x) =
        actualNormalizationResidueFieldMap A F Ω Q d
          (algebraMap (normalizationCommAlgCat A Ω) Q.ResidueField
            (arithmeticConstantNormalizationMap k A κ Ω x)) :=
      congrArg (actualNormalizationResidueFieldMap A F Ω Q d) (hcoeff x)
    _ = algebraMap (normalizationCommAlgCat A Ω) Q.ResidueField
        (normalizationGaloisRingHom A F Ω d.val
          (arithmeticConstantNormalizationMap k A κ Ω x)) :=
      actualNormalizationResidueFieldMap_coefficient A F Ω Q d
        (arithmeticConstantNormalizationMap k A κ Ω x)
    _ = algebraMap (normalizationCommAlgCat A Ω) Q.ResidueField
        (arithmeticConstantNormalizationMap k A κ Ω (δ x)) :=
      congrArg (algebraMap (normalizationCommAlgCat A Ω) Q.ResidueField) hconstant
    _ = c (δ x) := (hcoeff (δ x)).symm

variable {k F : Type} [Field k] [Field F] [Algebra k F]

/-- One and the same rational specialization retains its original integral
lift, full constant-root scaling, and the original decomposition action with
its literal restriction to the fixed coefficient field. -/
theorem exists_ordZero_rationalRootSpecialization_scaling_equivariant
    (v : Place k F) (hv : v.IsRational) (u : Fˣ) (hu : v.ord (u : F) = 0)
    (n : ℕ) (hn : IsUnit (n : k))
    (κ Ω : Type) [Field κ] [Field Ω]
    [Algebra k κ] [Algebra k Ω] [Algebra F Ω]
    [Algebra v.toValuationSubring Ω] [Algebra κ Ω]
    [IsScalarTower v.toValuationSubring F Ω]
    [IsScalarTower k v.toValuationSubring Ω]
    [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
    [IsAlgClosed κ] [Normal k κ]
    [IsGalois F Ω] [IsSepClosed Ω]
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [hQmax : Q.IsMaximal] :
    let nativeQ : Ideal (normalizationCommAlgCat v.toValuationSubring Ω) := Q
    letI : nativeQ.IsMaximal := hQmax
    let c : κ →+* IsLocalRing.ResidueField (Localization.AtPrime Q) :=
      (maximalQuotientResidueEquiv Q).toRingHom.comp
        (arithmeticConstantResidueMap k v.toValuationSubring κ Ω Q)
    ∃ E : {b : Ω // b ^ n = algebraMap F Ω (u : F)} ≃
        {b : κ // b ^ n = algebraMap k κ (ordZeroValue v hv u hu : k)},
      (∀ b, ∃ r : Localization.AtPrime Q,
        integralClosurePrimeToAmbientField v.toValuationSubring F Ω Q r = b.val ∧
          c (E b).val = IsLocalRing.residue (Localization.AtPrime Q) r) ∧
      (∀ (ζ : rootsOfUnity n κ) (b : {b : Ω // b ^ n = algebraMap F Ω (u : F)}),
        (E ⟨algebraMap κ Ω (ζ.val : κ) * b.val, by
          have hζ : (ζ.val : κ) ^ n = 1 :=
            congrArg (fun z : κˣ => (z : κ)) ((mem_rootsOfUnity _ _).mp ζ.property)
          rw [mul_pow, ← map_pow, hζ, map_one, one_mul, b.property]⟩).val =
            (ζ.val : κ) * (E b).val) ∧
      ∀ (d : (normalizationDecompositionGroup v.toValuationSubring F Ω nativeQ).carrier)
        (b : {b : Ω // b ^ n = algebraMap F Ω (u : F)}),
        (E ⟨d.val b.val, by rw [← map_pow, b.property, d.val.commutes]⟩).val =
          ((d.val.restrictScalars k).restrictNormal κ) (E b).val := by
  intro nativeQ
  let : nativeQ.IsMaximal := hQmax
  intro c
  obtain ⟨hc, _hconstants, _hvalue⟩ :=
    ordZero_normalizationResidue_constants v hv u hu κ Ω Q
  obtain ⟨E, hE, hscale⟩ :=
    exists_ordZero_rationalRootSpecialization_rootScaling v hv u hu n hn κ Ω Q
  obtain ⟨eNorm, hNorm, hNormAction⟩ :=
    exists_ordZero_normalizationRootSpecialization_equivariant v u hu n hn Ω Q
  have hmatch (b : {b : Ω // b ^ n = algebraMap F Ω (u : F)}) :
      (eNorm b).val = c (E b).val := by
    obtain ⟨r, hr, hred⟩ := hNorm b
    obtain ⟨s, hs, hsred⟩ := hE b
    have hrs : r = s :=
      integralClosurePrimeToAmbientField_injective v.toValuationSubring F Ω Q
        (hr.trans hs.symm)
    exact hred.trans ((congrArg (IsLocalRing.residue (Localization.AtPrime Q)) hrs).trans
      hsred.symm)
  refine ⟨E, hE, hscale, ?_⟩
  intro d b
  let b' : {b : Ω // b ^ n = algebraMap F Ω (u : F)} :=
    ⟨d.val b.val, by rw [← map_pow, b.property, d.val.commutes]⟩
  change (E b').val = ((d.val.restrictScalars k).restrictNormal κ) (E b).val
  apply hc.injective
  have haction : (eNorm b').val =
      actualNormalizationResidueFieldMap v.toValuationSubring F Ω nativeQ d (eNorm b).val :=
    hNormAction d b
  exact (hmatch b').symm.trans (haction.trans
    ((congrArg (actualNormalizationResidueFieldMap v.toValuationSubring F Ω nativeQ d)
      (hmatch b)).trans
        (canonicalConstantResidueMap_equivariant k v.toValuationSubring F κ Ω nativeQ d
          (E b).val)))

end AlgebraicCurve.Place
