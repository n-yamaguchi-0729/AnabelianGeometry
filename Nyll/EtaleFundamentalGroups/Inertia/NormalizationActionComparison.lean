/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationIntegralBaseInertia
public import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage

/-!
# Comparing the prescribed actions on the actual normalization

The normalization object and the raw integral closure have the same carrier.
Their action dictionaries must nevertheless be kept explicit when applying
raw fraction-field lemmas to native normalization groups. The coefficient
square of the original action proves the comparison below; no equality of
inertia groups is an input.
-/

@[expose] public section

noncomputable section

open SchemeTheory
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

universe uA uB u

attribute [local instance] normalizationCommAlgGaloisAction

section Action

variable {A : Type uA} {F Ω : Type u} [CommRing A] [Field F] [Field Ω]
  [Algebra A F] [IsFractionRing A F]
  [Algebra F Ω] [Algebra A Ω] [IsScalarTower A F Ω]
  [Algebra.IsAlgebraic F Ω]

/-- The original native action agrees with the prescribed fraction-field
restriction on each actual normalization coefficient. -/
theorem normalizationCommAlg_smul_eq_galRestrict
    (σ : Gal(Ω/F)) (b : normalizationCommAlgCat A Ω) :
    (show integralClosure A Ω from σ • b) =
      galRestrict A F Ω (integralClosure A Ω) σ b := by
  apply Subtype.ext
  have h := congrArg
    (fun f : normalizationCommAlgCat A Ω →+* Ω => f b)
    (normalizationCommAlg_action_comp_inclusion A F Ω σ)
  change σ (algebraMap (integralClosure A Ω) Ω
      (show integralClosure A Ω from b)) =
    algebraMap (integralClosure A Ω) Ω
      (show integralClosure A Ω from σ • b) at h
  exact h.symm.trans
    (algebraMap_galRestrict_apply A
      (K := F) (L := Ω) (B := integralClosure A Ω) σ b).symm

/-- Equality of inertia with both action dictionaries displayed explicitly.
The right side is the action used by the raw integral-base and finite-level
restriction theorems. -/
theorem normalizationCommAlg_inertia_eq_fractionFieldInertia
    (Q : Ideal (normalizationCommAlgCat A Ω)) :
    Q.inertia Gal(Ω/F) =
      (let : MulSemiringAction Gal(Ω/F) (integralClosure A Ω) :=
        IsIntegralClosure.MulSemiringAction A F Ω (integralClosure A Ω)
       Q.inertia Gal(Ω/F)) := by
  apply Subgroup.ext
  intro σ
  constructor
  · intro h b
    let bNative : normalizationCommAlgCat A Ω := b
    have hb : σ • bNative - bNative ∈ Q := h bNative
    have hsmul : (σ • bNative : normalizationCommAlgCat A Ω) =
        (show normalizationCommAlgCat A Ω from
          galRestrict A F Ω (integralClosure A Ω) σ bNative) :=
      normalizationCommAlg_smul_eq_galRestrict σ bNative
    exact (congrArg (fun z : normalizationCommAlgCat A Ω => z - bNative ∈ Q) hsmul).mp hb
  · intro h b
    have hb : (show normalizationCommAlgCat A Ω from
        galRestrict A F Ω (integralClosure A Ω) σ b) - b ∈ Q := h b
    have hsmul : (σ • b : normalizationCommAlgCat A Ω) =
        (show normalizationCommAlgCat A Ω from
          galRestrict A F Ω (integralClosure A Ω) σ b) :=
      normalizationCommAlg_smul_eq_galRestrict σ b
    exact (congrArg (fun z : normalizationCommAlgCat A Ω => z - b ∈ Q) hsmul).mpr hb

/-- The native prime stabilizer is the same original subgroup as the
fraction-field prime stabilizer. The comparison follows on ideal membership
from the proved equality of the two coefficient actions. -/
theorem normalizationCommAlg_stabilizer_eq_fractionFieldStabilizer
    (Q : Ideal (normalizationCommAlgCat A Ω)) :
    MulAction.stabilizer Gal(Ω/F) Q =
      (let : MulSemiringAction Gal(Ω/F) (integralClosure A Ω) :=
        IsIntegralClosure.MulSemiringAction A F Ω (integralClosure A Ω)
       MulAction.stabilizer Gal(Ω/F) Q) := by
  apply Subgroup.ext
  intro σ
  change (σ • Q = Q) ↔
    (let : MulSemiringAction Gal(Ω/F) (integralClosure A Ω) :=
      IsIntegralClosure.MulSemiringAction A F Ω (integralClosure A Ω)
     σ • Q = Q)
  have haction : σ • Q =
      (let : MulSemiringAction Gal(Ω/F) (integralClosure A Ω) :=
        IsIntegralClosure.MulSemiringAction A F Ω (integralClosure A Ω)
       σ • Q) := by
    apply Ideal.ext
    intro b
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  exact Iff.of_eq (congrArg (fun I : Ideal (normalizationCommAlgCat A Ω) => I = Q) haction)

end Action

section IntegralBase

variable {A : Type uA} {B : Type uB} {F L Ω : Type u}
  [CommRing A] [CommRing B] [Field F] [Field L] [Field Ω]
  [Algebra A B] [Algebra A Ω] [Algebra B Ω]
  [IsScalarTower A B Ω] [Algebra.IsIntegral A B]
  [Algebra A F] [IsFractionRing A F]
  [Algebra B L] [IsFractionRing B L]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω] [IsScalarTower A F Ω] [IsScalarTower B L Ω]
  [Algebra.IsAlgebraic F Ω] [Algebra.IsAlgebraic L Ω]

/-- Contracting the original normalization prime under integral base
enlargement preserves the original native inertia after scalar restriction.
The underlying coefficient identity, rather than a replacement action, is
the comparison with the existing fraction-field theorem. -/
theorem normalizationCommAlg_integralBase_inertia_comap
    (Q : Ideal (normalizationCommAlgCat A Ω)) :
    (Q.inertia Gal(Ω/F)).comap (AlgEquiv.restrictScalarsHom F) =
      (show Ideal (normalizationCommAlgCat B Ω) from
        Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom).inertia
          Gal(Ω/L) := by
  rw [normalizationCommAlg_inertia_eq_fractionFieldInertia (F := F) Q,
    normalizationCommAlg_inertia_eq_fractionFieldInertia (F := L)]
  exact normalizationIntegralBase_inertia_comap (A := A) (B := B) (Ω := Ω) F L Q

end IntegralBase

end EtaleFundamentalGroups.Inertia
