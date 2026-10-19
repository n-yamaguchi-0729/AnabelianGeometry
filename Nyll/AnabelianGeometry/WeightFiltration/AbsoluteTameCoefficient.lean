/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.TameCoefficientReduction
import Nyll.AnabelianGeometry.WeightFiltration.FiniteNormalizationCharZero
import Nyll.EtaleFundamentalGroups.Inertia.ActualAbsoluteTameCharacter
import Nyll.EtaleFundamentalGroups.Inertia.ActualTameCoordinateIdentity

/-!
# Full absolute tame coordinates and the actual residue coefficient

The existing full inverse-limit character has the same coefficient as the
local Kummer formula at every exponent. A single dominating finite tame
stage and the existing transition identities prove the comparison.
-/

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

universe u v w

attribute [local instance] Ideal.Quotient.field

/-- Every full absolute tame coordinate is the original coefficient in the prime residue field. -/
theorem actualAbsoluteTameCharacter_scalar_eq_tameCoefficient
    (A : Type u) (F : Type v) (Ω : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Field Ω] [Algebra A F] [IsFractionRing A F]
    [Algebra F Ω] [Algebra A Ω] [IsScalarTower A F Ω] [IsSepClosure F Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]
    [CharZero (IsLocalRing.ResidueField A)]
    (n : InvertibleExponent (IsLocalRing.ResidueField A))
    (τ : (actualNormalizationInertiaGroup A F Ω Q).carrier) :
    normalizationMaximalQuotientResidueEquiv A Ω Q
        (normalizationSeparableRootsScalar A Ω Q n
          ((actualAbsoluteTameCharacterMorphism A F Ω Q).hom' τ)) =
      tameCoefficient A F Ω Q n.val
        (isUnit_natCast_of_residue_charZero A n.val
          (InvertibleExponent.pos (IsLocalRing.ResidueField A) n).ne') τ := by
  let y := (actualAbsoluteTameCharacterMorphism A F Ω Q).hom' τ
  let e := normalizationMaximalQuotientResidueEquiv A Ω Q
  have hstage (E : FiniteGaloisIntermediateField F Ω) :
      e (normalizationSeparableRootsScalar A Ω Q (actualFiniteStageTameIndex A F Ω Q E) y) =
        (((actualFiniteTameCoordinate A F Ω Q E).hom' τ).val : Q.ResidueField) := by
    let m : Subtype (actualFiniteTameDegreeSet A F Ω Q) :=
      ⟨actualFiniteStageTameIndex A F Ω Q E, E, rfl⟩
    have hcancel : actualSeparableRootsComparison_apply A F Ω Q y =
        (actualTameCharacterMorphism A F Ω Q).hom' τ := by
      change (actualSeparableRootsComparison A F Ω Q)
        ((actualSeparableRootsComparison A F Ω Q).symm
          ((actualTameCharacterMorphism A F Ω Q).hom' τ)) = _
      exact (actualSeparableRootsComparison A F Ω Q).apply_symm_apply _
    have h : normalizationSeparableRootsScalar A Ω Q
        (actualFiniteStageTameIndex A F Ω Q E) y =
        ((actualTameCoordinate A F Ω Q m τ).val :
          (normalizationCommAlgCat A Ω).carrier ⧸ Q) := by
      calc
        _ = actualTameRootsScalar A F Ω Q m
            (actualSeparableRootsComparison_apply A F Ω Q y) :=
          (actualSeparableRootsComparison_scalar A F Ω Q m y).symm
        _ = actualTameRootsScalar A F Ω Q m
            ((actualTameCharacterMorphism A F Ω Q).hom' τ) :=
          congrArg (actualTameRootsScalar A F Ω Q m) hcancel
        _ = _ := actualTameRootsScalar_character A F Ω Q m τ
    have hat := actualTameCoordinate_at_stage A F Ω Q E τ
    have hatScalar := congrArg (fun r : rootsOfUnity
      (actualFiniteStageTameOrder A F Ω Q E)
      ((normalizationCommAlgCat A Ω).carrier ⧸ Q) =>
        (r.val : (normalizationCommAlgCat A Ω).carrier ⧸ Q)) hat
    exact (congrArg e (h.trans hatScalar)).trans (e.apply_symm_apply _)
  let hnA := isUnit_natCast_of_residue_charZero A n.val
    (InvertibleExponent.pos (IsLocalRing.ResidueField A) n).ne'
  obtain ⟨E, hE⟩ := exists_actualFiniteStageTameOrder_multiple A F Ω Q n.val hnA
  let N := actualFiniteStageTameIndex A F Ω Q E
  let s := nativeSeparableRootsInclusionEquiv (IsLocalRing.ResidueField A)
    (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q)
  let z := s y
  have hcompat := (primeToRootsSystem (IsLocalRing.ResidueField A)
    ((normalizationCommAlgCat A Ω).carrier ⧸ Q)).projection_compatible z n N hE
  have h := congrArg (fun r : rootsOfUnity n.val
    ((normalizationCommAlgCat A Ω).carrier ⧸ Q) => (r.val :
      (normalizationCommAlgCat A Ω).carrier ⧸ Q)) hcompat
  change nativeFullRootsScalar (IsLocalRing.ResidueField A)
      (normalizationResidueFieldObject A Ω Q) N z ^ (N.val / n.val) =
    nativeFullRootsScalar (IsLocalRing.ResidueField A)
      (normalizationResidueFieldObject A Ω Q) n z at h
  have hcoord (i : InvertibleExponent (IsLocalRing.ResidueField A)) :=
    nativeSeparableRootsInclusionEquiv_scalar (IsLocalRing.ResidueField A)
      (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q) i y
  have hs : normalizationSeparableRootsScalar A Ω Q n y =
      normalizationSeparableRootsScalar A Ω Q N y ^ (N.val / n.val) :=
    (hcoord n).symm.trans (h.symm.trans
      (congrArg (fun a => a ^ (N.val / n.val)) (hcoord N)))
  change e (normalizationSeparableRootsScalar A Ω Q n y) = _
  calc
    _ = e (normalizationSeparableRootsScalar A Ω Q N y ^ (N.val / n.val)) :=
      congrArg e hs
    _ = e (normalizationSeparableRootsScalar A Ω Q N y) ^ (N.val / n.val) :=
      map_pow e _ _
    _ = (((actualFiniteTameCoordinate A F Ω Q E).hom' τ).val : Q.ResidueField) ^
        (N.val / n.val) := congrArg (fun a => a ^ (N.val / n.val)) (hstage E)
    _ = _ := (tameCoefficient_eq_finite A F Ω Q n.val hnA E hE τ).symm

end AnabelianGeometry.WeightFiltration
