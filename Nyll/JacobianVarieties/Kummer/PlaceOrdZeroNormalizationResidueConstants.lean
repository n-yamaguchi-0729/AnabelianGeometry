/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.PlaceOrdZeroKummerCover
import Nyll.EtaleFundamentalGroups.Inertia.RationalCuspDecompositionConstants
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeEmbedding
import Nyll.SchemeTheory.RingTheory.Ramification.NativeMaximalResidue

/-!
# The unchanged rational value in the original normalization residue field

The constant map is the prescribed embedding into the normalization, followed
by its quotient and the canonical maximal-quotient-to-localization-residue map.
Rationality supplies the residue retraction internally. Thus the specialized
local Kummer coefficient is the image of the actual value of the same function.
-/

noncomputable section

open EtaleFundamentalGroups.Inertia EtaleFundamentalGroups.StrictHenselian

namespace AlgebraicCurve.Place

variable {k F : Type} [Field k] [Field F] [Algebra k F]

/-- The canonical constant map into the literal normalization localization's
residue field is bijective and carries the actual rational value to the
specialized unchanged local coefficient. All coefficient identifications are
derived from the prescribed constant embedding and the original place. -/
theorem ordZero_normalizationResidue_constants
    (v : Place k F) (hv : v.IsRational) (u : Fˣ) (hu : v.ord (u : F) = 0)
    (κ Ω : Type) [Field κ] [Field Ω]
    [Algebra k κ] [Algebra k Ω] [Algebra v.toValuationSubring Ω] [Algebra κ Ω]
    [IsScalarTower k v.toValuationSubring Ω] [IsScalarTower k κ Ω]
    [Algebra.IsAlgebraic k κ] [IsAlgClosed κ]
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [Q.IsMaximal] :
    let c : κ →+* IsLocalRing.ResidueField (Localization.AtPrime Q) :=
      (maximalQuotientResidueEquiv Q).toRingHom.comp
        (arithmeticConstantResidueMap k v.toValuationSubring κ Ω Q)
    Function.Bijective c ∧
      (∀ z : κ, c z = IsLocalRing.residue (Localization.AtPrime Q)
        (algebraMap (integralClosure v.toValuationSubring Ω) (Localization.AtPrime Q)
          (arithmeticConstantNormalizationMap k v.toValuationSubring κ Ω z))) ∧
      IsLocalRing.residue (Localization.AtPrime Q)
          (integralClosurePrimeBaseMap v.toValuationSubring Ω Q
            (ordZeroUnit v u hu : v.toValuationSubring)) =
        c (algebraMap k κ (ordZeroValue v hv u hu : k)) := by
  intro c
  let nativeQ : Ideal (SchemeTheory.normalizationCommAlgCat v.toValuationSubring Ω) := Q
  let : nativeQ.IsMaximal := (inferInstance : Q.IsMaximal)
  let e : k ≃ₐ[k] v.ResidueField :=
    AlgEquiv.ofBijective (Algebra.ofId k v.ResidueField)
      ⟨v.algebraMap_residueField_injective, hv⟩
  let r : v.toValuationSubring →ₐ[k] k := e.symm.toAlgHom.comp
    (IsScalarTower.toAlgHom k v.toValuationSubring v.ResidueField)
  have hr : RingHom.ker r.toRingHom = IsLocalRing.maximalIdeal v.toValuationSubring := by
    ext a
    change e.symm (IsLocalRing.residue v.toValuationSubring a) = 0 ↔
      a ∈ IsLocalRing.maximalIdeal v.toValuationSubring
    rw [← IsLocalRing.residue_eq_zero_iff]
    constructor
    · intro h
      exact e.symm.injective (h.trans (map_zero e.symm).symm)
    · intro h
      rw [h, map_zero]
  have hrvalue : r (ordZeroUnit v u hu : v.toValuationSubring) = (ordZeroValue v hv u hu : k) := by
    apply e.injective
    change e (e.symm (IsLocalRing.residue v.toValuationSubring
      (ordZeroUnit v u hu : v.toValuationSubring))) =
      algebraMap k v.ResidueField (ordZeroValue v hv u hu : k)
    rw [e.apply_symm_apply]
    exact ordZeroUnit_residue v hv u hu
  have hcoeff (b : integralClosure v.toValuationSubring Ω) :
      maximalQuotientResidueEquiv Q (Ideal.Quotient.mk Q b) =
        IsLocalRing.residue (Localization.AtPrime Q)
          (algebraMap (integralClosure v.toValuationSubring Ω) (Localization.AtPrime Q) b) := by
    exact (RingHom.congr_fun (maximalQuotientResidueEquiv_comp_quotient Q) b).trans
      (show algebraMap (integralClosure v.toValuationSubring Ω)
          (IsLocalRing.ResidueField (Localization.AtPrime Q)) b =
        IsLocalRing.residue (Localization.AtPrime Q)
          (algebraMap (integralClosure v.toValuationSubring Ω) (Localization.AtPrime Q) b) from rfl)
  refine ⟨(maximalQuotientResidueEquiv Q).bijective.comp
    (arithmeticConstantResidueMap_bijective k v.toValuationSubring κ Ω nativeQ r hr), ?_, ?_⟩
  · intro z
    exact hcoeff (arithmeticConstantNormalizationMap k v.toValuationSubring κ Ω z)
  · have hquot := arithmeticConstantResidueMap_coefficient k v.toValuationSubring κ Ω nativeQ r hr
      (ordZeroUnit v u hu : v.toValuationSubring)
    rw [hrvalue] at hquot
    exact (hcoeff (algebraMap v.toValuationSubring (integralClosure v.toValuationSubring Ω)
      (ordZeroUnit v u hu : v.toValuationSubring))).symm.trans
      (congrArg (maximalQuotientResidueEquiv Q) hquot)

end AlgebraicCurve.Place
