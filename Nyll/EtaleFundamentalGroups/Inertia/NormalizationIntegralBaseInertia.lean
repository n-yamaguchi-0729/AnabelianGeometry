/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.IntegralClosure.IntegralBase.Equiv
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.Algebra.Algebra.Tower

/-!
# Inertia under an integral enlargement of the base

The canonical equivalence of the two normalizations is the identity in the
same ambient field and intertwines the original Galois actions. Contracting
the same prime along it identifies inertia with the scalar-restriction comap.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe uA uB u

variable (A : Type uA) (B : Type uB) (Ω : Type u)
  [CommRing A] [CommRing B] [Field Ω]
  [Algebra A B] [Algebra A Ω] [Algebra B Ω]
  [IsScalarTower A B Ω] [Algebra.IsIntegral A B]

/-- The canonical normalization comparison, retaining its literal ring map. -/
def normalizationIntegralBaseRingEquiv :
    integralClosure B Ω ≃+* integralClosure A Ω := by
  let : Algebra B (integralClosure A Ω) :=
    integralClosureIntegralBaseAlgebra
  exact integralClosureIntegralBaseAlgEquiv.toRingEquiv

/-- The comparison does not change the element of the ambient field. -/
theorem normalizationIntegralBaseRingEquiv_toAmbient
    (b : integralClosure B Ω) :
    algebraMap (integralClosure A Ω) Ω (normalizationIntegralBaseRingEquiv A B Ω b) =
      algebraMap (integralClosure B Ω) Ω b := by
  exact algebraMap_integralClosureIntegralBaseAlgEquiv b

variable {A B Ω}
variable (F L : Type u) [Field F] [Field L]
  [Algebra A F] [IsFractionRing A F]
  [Algebra B L] [IsFractionRing B L]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω] [IsScalarTower A F Ω] [IsScalarTower B L Ω]
  [Algebra.IsAlgebraic F Ω] [Algebra.IsAlgebraic L Ω]

local instance originalNormalizationAction :
    MulSemiringAction Gal(Ω/F) (integralClosure A Ω) :=
  IsIntegralClosure.MulSemiringAction A F Ω (integralClosure A Ω)

local instance enlargedNormalizationAction :
    MulSemiringAction Gal(Ω/L) (integralClosure B Ω) :=
  IsIntegralClosure.MulSemiringAction B L Ω (integralClosure B Ω)

/-- The canonical comparison intertwines the two prescribed Galois actions. -/
theorem normalizationIntegralBaseRingEquiv_smul
    (σ : Gal(Ω/L)) (b : integralClosure B Ω) :
    normalizationIntegralBaseRingEquiv A B Ω (σ • b) =
      (σ.restrictScalars F) • normalizationIntegralBaseRingEquiv A B Ω b := by
  apply (IsIntegralClosure.algebraMap_injective (integralClosure A Ω) A Ω)
  calc
    algebraMap (integralClosure A Ω) Ω
        (normalizationIntegralBaseRingEquiv A B Ω (σ • b)) =
      algebraMap (integralClosure B Ω) Ω (σ • b) :=
        normalizationIntegralBaseRingEquiv_toAmbient A B Ω (σ • b)
    _ = σ (algebraMap (integralClosure B Ω) Ω b) :=
      algebraMap_galRestrict_apply B σ b
    _ = (σ.restrictScalars F)
        (algebraMap (integralClosure A Ω) Ω
          (normalizationIntegralBaseRingEquiv A B Ω b)) :=
      congrArg σ (normalizationIntegralBaseRingEquiv_toAmbient A B Ω b).symm
    _ = algebraMap (integralClosure A Ω) Ω
        ((σ.restrictScalars F) • normalizationIntegralBaseRingEquiv A B Ω b) :=
      (algebraMap_galRestrict_apply A (σ.restrictScalars F) _).symm

/-- Inertia for the same prime after integral base enlargement is precisely
the comap under restriction of scalars. No inertia equality is an input. -/
theorem normalizationIntegralBase_inertia_comap
    (Q : Ideal (integralClosure A Ω)) :
    (Q.inertia Gal(Ω/F)).comap (AlgEquiv.restrictScalarsHom F) =
      (Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom).inertia Gal(Ω/L) := by
  let e := normalizationIntegralBaseRingEquiv A B Ω
  ext σ
  constructor
  · intro h b
    change e (σ • b - b) ∈ Q
    rw [map_sub, normalizationIntegralBaseRingEquiv_smul F L]
    exact h (e b)
  · intro h a
    obtain ⟨b, rfl⟩ := e.surjective a
    have hb := h b
    change e (σ • b - b) ∈ Q at hb
    rw [map_sub, normalizationIntegralBaseRingEquiv_smul F L] at hb
    exact hb

end EtaleFundamentalGroups.Inertia
