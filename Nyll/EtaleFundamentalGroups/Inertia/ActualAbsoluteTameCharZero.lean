/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualAbsoluteTameCharacter
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationWildCharZero
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaCompact
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# The actual inertia character in residue characteristic zero

Triviality of the original wild subgroup makes the existing absolute tame
character a continuous equivalence, with its original forward map.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (Ω : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
  [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosure K Ω]
  (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]
  [CharZero (IsLocalRing.ResidueField A)]

/-- In residue characteristic zero, the original absolute tame character is an equivalence. -/
def actualAbsoluteTameCharacterEquivOfCharZero :
    (actualNormalizationInertiaGroup A K Ω Q).carrier ≃ₜ*
      (normalizationSeparableRootsGroup A Ω Q).carrier := by
  let : CompactSpace (actualNormalizationInertiaGroup A K Ω Q).carrier :=
    actualNormalizationInertia_compactSpace A K Ω Q
  let : T2Space (normalizationSeparableRootsGroup A Ω Q).carrier :=
    inferInstanceAs (T2Space (primeToRootsSystem (IsLocalRing.ResidueField A)
      (nativeSeparableResidueField (IsLocalRing.ResidueField A)
        (normalizationResidueFieldObject A Ω Q)
        (normalizationResidueFieldAlgebra A Ω Q)).α).inverseLimit)
  apply ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    (actualAbsoluteTameCharacterMorphism A K Ω Q).hom'
    (actualAbsoluteTameCharacter_continuous A K Ω Q)
  refine ⟨?_, actualAbsoluteTameCharacter_surjective A K Ω Q⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [actualAbsoluteTameCharacter_ker,
    actualNormalizationWildSubgroup_eq_bot_of_baseResidue_charZero]

/-- The equivalence uses the original absolute tame character on each inertia element. -/
theorem actualAbsoluteTameCharacterEquivOfCharZero_apply
    (σ : (actualNormalizationInertiaGroup A K Ω Q).carrier) :
    actualAbsoluteTameCharacterEquivOfCharZero A K Ω Q σ =
      (actualAbsoluteTameCharacterMorphism A K Ω Q).hom' σ := rfl

end EtaleFundamentalGroups.Inertia
