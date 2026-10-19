/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.PlaceOrdZeroRationalRootSpecialization
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Full constant-root scaling for the same rational specialization

Retain the existing equivalence and its literal integral-lift evaluation.
Each constant root of unity has its prescribed integral normalization image.
Uniqueness of lifts identifies scaling before reduction with multiplication
by this image; injectivity of the canonical constant residue map then gives
the same full roots-of-unity action in the fixed constant field.
-/

noncomputable section

open EtaleFundamentalGroups.Inertia EtaleFundamentalGroups.StrictHenselian

namespace AlgebraicCurve.Place

variable {k F : Type} [Field k] [Field F] [Algebra k F]

/-- The existing rational specialization retains its actual lift evaluation
and intertwines multiplication by every root of unity in the fixed constants.
The same equivalence witnesses both conclusions. -/
theorem exists_ordZero_rationalRootSpecialization_rootScaling
    (v : Place k F) (hv : v.IsRational) (u : Fˣ) (hu : v.ord (u : F) = 0)
    (n : ℕ) (hn : IsUnit (n : k))
    (κ Ω : Type) [Field κ] [Field Ω]
    [Algebra k κ] [Algebra k Ω] [Algebra F Ω]
    [Algebra v.toValuationSubring Ω] [Algebra κ Ω]
    [IsScalarTower v.toValuationSubring F Ω]
    [IsScalarTower k v.toValuationSubring Ω] [IsScalarTower k κ Ω]
    [Algebra.IsAlgebraic k κ] [IsAlgClosed κ]
    [Algebra.IsAlgebraic F Ω] [IsSepClosed Ω]
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [Q.IsMaximal] :
    let c : κ →+* IsLocalRing.ResidueField (Localization.AtPrime Q) :=
      (maximalQuotientResidueEquiv Q).toRingHom.comp
        (arithmeticConstantResidueMap k v.toValuationSubring κ Ω Q)
    ∃ E : {b : Ω // b ^ n = algebraMap F Ω (u : F)} ≃
        {b : κ // b ^ n = algebraMap k κ (ordZeroValue v hv u hu : k)},
      (∀ b, ∃ r : Localization.AtPrime Q,
        integralClosurePrimeToAmbientField v.toValuationSubring F Ω Q r = b.val ∧
          c (E b).val = IsLocalRing.residue (Localization.AtPrime Q) r) ∧
      ∀ (ζ : rootsOfUnity n κ) (b : {b : Ω // b ^ n = algebraMap F Ω (u : F)}),
        (E ⟨algebraMap κ Ω (ζ.val : κ) * b.val, by
          have hζ : (ζ.val : κ) ^ n = 1 :=
            congrArg (fun z : κˣ => (z : κ)) ((mem_rootsOfUnity _ _).mp ζ.property)
          rw [mul_pow, ← map_pow, hζ, map_one, one_mul, b.property]⟩).val =
            (ζ.val : κ) * (E b).val := by
  intro c
  obtain ⟨hc, hconst, _hvalue⟩ := ordZero_normalizationResidue_constants v hv u hu κ Ω Q
  obtain ⟨E, hE⟩ := exists_ordZero_rationalRootSpecialization v hv u hu n hn κ Ω Q
  refine ⟨E, hE, ?_⟩
  intro ζ b
  have hζ : (ζ.val : κ) ^ n = 1 :=
    congrArg (fun z : κˣ => (z : κ)) ((mem_rootsOfUnity _ _).mp ζ.property)
  let b' : {b : Ω // b ^ n = algebraMap F Ω (u : F)} :=
    ⟨algebraMap κ Ω (ζ.val : κ) * b.val, by
      rw [mul_pow, ← map_pow, hζ, map_one, one_mul, b.property]⟩
  let ζR : Localization.AtPrime Q :=
    algebraMap (integralClosure v.toValuationSubring Ω) (Localization.AtPrime Q)
      (arithmeticConstantNormalizationMap k v.toValuationSubring κ Ω (ζ.val : κ))
  have hζambient :
      integralClosurePrimeToAmbientField v.toValuationSubring F Ω Q ζR =
        algebraMap κ Ω (ζ.val : κ) :=
    RingHom.congr_fun
      (integralClosurePrimeToAmbientField_comp_coefficient v.toValuationSubring F Ω Q)
      (arithmeticConstantNormalizationMap k v.toValuationSubring κ Ω (ζ.val : κ))
  have hζresidue : IsLocalRing.residue (Localization.AtPrime Q) ζR = c (ζ.val : κ) :=
    (hconst (ζ.val : κ)).symm
  obtain ⟨r, hr, hred⟩ := hE b
  obtain ⟨r', hr', hred'⟩ := hE b'
  have hlift : r' = ζR * r := by
    apply integralClosurePrimeToAmbientField_injective v.toValuationSubring F Ω Q
    calc
      integralClosurePrimeToAmbientField v.toValuationSubring F Ω Q r' =
          algebraMap κ Ω (ζ.val : κ) * b.val := hr'
      _ = integralClosurePrimeToAmbientField v.toValuationSubring F Ω Q ζR *
          integralClosurePrimeToAmbientField v.toValuationSubring F Ω Q r := by
        rw [hζambient, hr]
      _ = integralClosurePrimeToAmbientField v.toValuationSubring F Ω Q (ζR * r) :=
        (map_mul (integralClosurePrimeToAmbientField v.toValuationSubring F Ω Q) ζR r).symm
  change (E b').val = (ζ.val : κ) * (E b).val
  apply hc.injective
  calc
    c (E b').val = IsLocalRing.residue (Localization.AtPrime Q) r' := hred'
    _ = IsLocalRing.residue (Localization.AtPrime Q) ζR *
        IsLocalRing.residue (Localization.AtPrime Q) r := by rw [hlift, map_mul]
    _ = c (ζ.val : κ) * c (E b).val := by rw [hζresidue, hred]
    _ = c ((ζ.val : κ) * (E b).val) := (map_mul c _ _).symm

end AlgebraicCurve.Place
