/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.PlaceLocalValuation
import Nyll.AnabelianGeometry.WeightFiltration.AbsoluteTameCoefficient
import Nyll.AnabelianGeometry.WeightFiltration.FiniteNormalizationBaseCoefficients
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationConstantRoots
import Nyll.EtaleFundamentalGroups.Inertia.ActualAbsoluteTameCharZero

/-!
# Common constant-root parameters for actual place inertia

Every place uses the same full roots limit of the constant field. The
coordinate formula compares this parameter with the original tame
coefficient used to evaluate actual finite étale cohomology characters.
-/

noncomputable section

open AlgebraicCurve SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

variable (k F Ω : Type) [Field k] [CharZero k] [IsSepClosed k] [Field F] [Field Ω]
  [Algebra k F] [Algebra F Ω] [IsSepClosure F Ω]
  (p : Place k F) [Algebra p.toValuationSubring Ω]
  [IsScalarTower p.toValuationSubring F Ω]
  (Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω).carrier) [Q.IsMaximal]

/-- Actual inertia at any place is parametrized by the same constant roots limit. -/
def placeInertiaConstantRootsEquiv :
    (primeToRootsSystem k k).inverseLimit ≃ₜ*
      (actualNormalizationInertiaGroup p.toValuationSubring F Ω Q).carrier := by
  let : CharZero p.ResidueField := place_residueField_charZero p
  exact (normalizationConstantRootsEquiv k p.toValuationSubring Ω Q).trans
    (actualAbsoluteTameCharacterEquivOfCharZero p.toValuationSubring F Ω Q).symm

/-- The common parameter recovers the actual local tame coefficient at every exponent. -/
theorem placeInertiaConstantRootsEquiv_tameCoefficient
    (n : InvertibleExponent k) (x : (primeToRootsSystem k k).inverseLimit) :
    let _ : CharZero p.ResidueField := place_residueField_charZero p
    let hnA := isUnit_natCast_of_residue_charZero p.toValuationSubring n.val
      (InvertibleExponent.pos k n).ne'
    (normalizationBaseResidue p.toValuationSubring Ω Q).comp
        (algebraMap k p.toValuationSubring)
        (((primeToRootsSystem k k).projection n x).val : k) =
      tameCoefficient p.toValuationSubring F Ω Q n.val hnA
        (placeInertiaConstantRootsEquiv k F Ω p Q x) := by
  intro charZero hnA
  let m := InvertibleExponent.charZeroOrderIso k p.ResidueField n
  let τ := placeInertiaConstantRootsEquiv k F Ω p Q x
  have hc : (actualAbsoluteTameCharacterMorphism p.toValuationSubring F Ω Q).hom' τ =
      normalizationConstantRootsEquiv k p.toValuationSubring Ω Q x :=
    (actualAbsoluteTameCharacterEquivOfCharZero p.toValuationSubring F Ω Q).apply_symm_apply _
  have h := actualAbsoluteTameCharacter_scalar_eq_tameCoefficient
    p.toValuationSubring F Ω Q m τ
  rw [hc, normalizationConstantRootsEquiv_scalar] at h
  apply Eq.trans ?_ h
  symm
  change normalizationMaximalQuotientResidueEquiv p.toValuationSubring Ω Q
    (Ideal.Quotient.mk Q (algebraMap p.toValuationSubring
      (normalizationCommAlgCat p.toValuationSubring Ω)
      (algebraMap k p.toValuationSubring
        (((primeToRootsSystem k k).projection n x).val : k)))) = _
  have he := RingHom.congr_fun
    (normalizationMaximalQuotientResidueEquiv_comp_quotient p.toValuationSubring Ω Q)
    (algebraMap p.toValuationSubring (normalizationCommAlgCat p.toValuationSubring Ω)
      (algebraMap k p.toValuationSubring
        (((primeToRootsSystem k k).projection n x).val : k)))
  exact he

end AnabelianGeometry.WeightFiltration
