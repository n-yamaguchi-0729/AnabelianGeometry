/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteNormalizationPrime
import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage

/-!
# Full inertia image for an abstract finite normal subextension

The finite field need not be presented as a literal intermediate field.
Its prescribed embedding selects the same contraction of the absolute
normalization prime, and restriction has exactly that inertia image.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe uA u

variable {A : Type uA} {K L Ω : Type u}
  [CommRing A] [Field K] [Field L] [Field Ω]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]
  [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω]
  [Algebra L Ω] [IsScalarTower K L Ω] [IsScalarTower A L Ω]
  [IsGalois K Ω]

local instance finiteNormalizationAction :
    MulSemiringAction Gal(L/K) (integralClosure A L) :=
  IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)

local instance absoluteNormalizationAction :
    MulSemiringAction Gal(Ω/K) (integralClosure A Ω) :=
  IsIntegralClosure.MulSemiringAction A K Ω (integralClosure A Ω)

/-- Restriction of absolute inertia is the full inertia of the literal
contracted prime for the given finite-field embedding. -/
theorem absoluteNormalizationPrime_inertia_map_eq_contraction
    (Q : Ideal (integralClosure A Ω)) [Q.IsPrime] :
    (Q.inertia Gal(Ω/K)).map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L) =
      (absoluteNormalizationPrimeContraction
        (A := A) (L := L) (Omega := Ω) Q).inertia Gal(L/K) := by
  let j := IsScalarTower.toAlgHom K L Ω
  let E : IntermediateField K Ω := j.fieldRange
  have : FiniteDimensional K E := FiniteDimensional.of_injective
    j.equivFieldRange.symm.toLinearMap j.equivFieldRange.symm.injective
  let H := E.fixingSubgroup
  let : Algebra (integralClosure A L) (integralClosure A Ω) :=
    (IsScalarTower.toAlgHom A L Ω).mapIntegralClosure.toRingHom.toAlgebra
  let : TopologicalSpace (integralClosure A Ω) := ⊥
  have : DiscreteTopology (integralClosure A Ω) := ⟨rfl⟩
  have : ContinuousSMul Gal(Ω/K) (integralClosure A Ω) :=
    integralClosure_continuousSMul_krull A K Ω
  have : CompactSpace H :=
    isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed E).isCompact
  have : Algebra.IsInvariant (integralClosure A L) (integralClosure A Ω) H := by
    constructor
    intro b hb
    have hbE : (b : Ω) ∈ E := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup E]
      apply (IntermediateField.mem_fixedField_iff E.fixingSubgroup (b : Ω)).mpr
      intro σ hσ
      have h := hb ⟨σ, hσ⟩
      change galRestrict A K Ω (integralClosure A Ω) σ b = b at h
      exact (algebraMap_galRestrict_apply A σ b).symm.trans
        (congrArg Subtype.val h)
    obtain ⟨l, hl⟩ := hbE
    have hleq : j l = (b : Ω) := hl
    have he : IsIntegral A l :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom A L Ω)
        (algebraMap L Ω).injective).mp (by
          change IsIntegral A (j l)
          rw [hleq]
          exact b.property)
    refine ⟨⟨l, he⟩, ?_⟩
    apply Subtype.ext
    exact hl
  have hker : H ≤
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker := by
    intro σ hσ
    apply AlgEquiv.ext
    intro l
    apply j.injective
    calc
      j (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L σ l) =
          σ (j l) := AlgEquiv.restrictNormal_commutes σ L l
      _ = j l := hσ ⟨j l, ⟨l, rfl⟩⟩
  have hcompat : ∀ (σ : Gal(Ω/K)) (b : integralClosure A L),
      algebraMap (integralClosure A L) (integralClosure A Ω)
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L σ • b) =
        σ • algebraMap (integralClosure A L) (integralClosure A Ω) b := by
    intro σ b
    apply Subtype.ext
    change algebraMap L Ω
        (algebraMap (integralClosure A L) L
          (galRestrict A K L (integralClosure A L)
            (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L σ) b)) =
      algebraMap (integralClosure A Ω) Ω
        (galRestrict A K Ω (integralClosure A Ω) σ
          ((IsScalarTower.toAlgHom A L Ω).mapIntegralClosure b))
    rw [algebraMap_galRestrict_apply A, algebraMap_galRestrict_apply A]
    exact AlgEquiv.restrictNormal_commutes σ L
      (algebraMap (integralClosure A L) L b)
  exact SchemeTheory.map_inertia_of_surjective_of_profinite
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L) H
    (Q.under (integralClosure A L)) Q
    (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) Ω)
    hker hcompat

end EtaleFundamentalGroups.Inertia
