/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.PlaceOrdZeroNormalizationRootSpecialization
import Nyll.JacobianVarieties.Kummer.PlaceOrdZeroNormalizationResidueConstants

/-!
# Specialization to roots of the actual rational value

The root is reduced in the original normalization localization, then read
back in the fixed algebraic constants through the canonical residue map.
The rational coefficient is the existing evalAt of the unchanged function.
-/

noncomputable section
open EtaleFundamentalGroups.Inertia EtaleFundamentalGroups.StrictHenselian

namespace AlgebraicCurve.Place

variable {k F : Type} [Field k] [Field F] [Algebra k F]

/-- Specialization of the unchanged generic roots to the roots of their
actual rational value, retaining the literal normalization reduction. -/
theorem exists_ordZero_rationalRootSpecialization
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
      ∀ b, ∃ r : Localization.AtPrime Q,
        integralClosurePrimeToAmbientField v.toValuationSubring F Ω Q r = b.val ∧
          c (E b).val = IsLocalRing.residue (Localization.AtPrime Q) r := by
  intro c
  obtain ⟨hc, _hconst, hvalue⟩ := ordZero_normalizationResidue_constants v hv u hu κ Ω Q
  obtain ⟨e, he⟩ := exists_ordZero_normalizationRootSpecialization v u hu n hn Ω Q
  let C := RingEquiv.ofBijective c hc
  let a : κ := algebraMap k κ (ordZeroValue v hv u hu : k)
  let d := IsLocalRing.residue (Localization.AtPrime Q)
    (integralClosurePrimeBaseMap v.toValuationSubring Ω Q
      (ordZeroUnit v u hu : v.toValuationSubring))
  have hCa : C a = d := hvalue.symm
  let EC : {b : IsLocalRing.ResidueField (Localization.AtPrime Q) // b ^ n = d} ≃
      {b : κ // b ^ n = a} := {
    toFun := fun b => ⟨C.symm b.val, by
      apply C.injective
      rw [map_pow, C.apply_symm_apply, b.property, hCa]⟩
    invFun := fun b => ⟨C b.val, by rw [← map_pow, b.property, hCa]⟩
    left_inv := fun b => Subtype.ext (C.apply_symm_apply b.val)
    right_inv := fun b => Subtype.ext (C.symm_apply_apply b.val) }
  refine ⟨e.trans EC, ?_⟩
  intro b
  obtain ⟨r, hr, hred⟩ := he b
  refine ⟨r, hr, ?_⟩
  exact (C.apply_symm_apply (e b).val).trans hred

end AlgebraicCurve.Place
