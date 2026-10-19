/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteNormalizationPrime

/-!
# Equivariance of contraction of actual normalization primes
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open scoped Pointwise

universe uA u

variable {A : Type uA} {K L Omega : Type u}
variable [CommRing A]
variable [Field K] [Field L] [Field Omega]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]
variable [FiniteDimensional K L] [_root_.IsGalois K L]
variable [Algebra K Omega] [Algebra A Omega] [IsScalarTower A K Omega]
variable [Algebra L Omega] [IsScalarTower K L Omega]
variable [IsScalarTower A L Omega]
variable [Algebra.IsAlgebraic K Omega]

local notation "B" => integralClosure A L
local notation "C" => integralClosure A Omega


local instance contractionFiniteGaloisAction :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

local instance contractionAbsoluteGaloisAction :
    MulSemiringAction Gal(Omega/K) C :=
  IsIntegralClosure.MulSemiringAction A K Omega C


omit [FiniteDimensional K L] in
/-- The coefficient inclusion intertwines the actual Galois actions. -/
theorem finiteNormalizationToAbsoluteNormalization_smul
    (sigma : Gal(Omega/K)) (x : B) :
    (finiteNormalizationToAbsoluteNormalization
      (A := A) (L := L) (Omega := Omega))
        ((AlgEquiv.restrictNormalHom (F := K) (K₁ := Omega) L sigma) • x) =
      sigma • (finiteNormalizationToAbsoluteNormalization
        (A := A) (L := L) (Omega := Omega)) x := by
  apply Subtype.ext
  change
    algebraMap L Omega
        (algebraMap B L
          (galRestrict A K L B
            (AlgEquiv.restrictNormalHom (F := K) (K₁ := Omega) L sigma) x)) =
      algebraMap C Omega
        (galRestrict A K Omega C sigma
          ((finiteNormalizationToAbsoluteNormalization
            (A := A) (L := L) (Omega := Omega)) x))
  rw [algebraMap_galRestrict_apply A, algebraMap_galRestrict_apply A]
  exact
    (AlgEquiv.restrictNormal_commutes sigma L
      (algebraMap B L x)).trans (by rfl)

omit [FiniteDimensional K L] in
/-- Contraction carries the translated original prime to the translated finite prime. -/
theorem absoluteNormalizationPrimeContraction_smul
    (Q : Ideal C) (sigma : Gal(Omega/K)) :
    absoluteNormalizationPrimeContraction (A := A) (L := L) (Omega := Omega)
        (sigma • Q) =
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Omega) L sigma) •
        absoluteNormalizationPrimeContraction (A := A) (L := L) (Omega := Omega) Q := by
  ext x
  change (finiteNormalizationToAbsoluteNormalization
    (A := A) (L := L) (Omega := Omega)) x ∈ sigma • Q ↔ _
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  change sigma⁻¹ • (finiteNormalizationToAbsoluteNormalization
    (A := A) (L := L) (Omega := Omega)) x ∈ Q ↔
      (finiteNormalizationToAbsoluteNormalization
        (A := A) (L := L) (Omega := Omega))
        ((AlgEquiv.restrictNormalHom (F := K) (K₁ := Omega) L sigma)⁻¹ • x) ∈ Q
  rw [← map_inv, finiteNormalizationToAbsoluteNormalization_smul]

end EtaleFundamentalGroups.Inertia
