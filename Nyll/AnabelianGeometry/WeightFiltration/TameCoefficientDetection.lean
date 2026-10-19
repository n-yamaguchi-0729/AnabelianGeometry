/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.TameCoefficientReduction
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameSurjectivity

/-!
# Primitive values and detection by tame coefficients

The actual inertia coefficient attains a primitive root at every invertible
exponent. Its powers therefore detect divisibility by that exponent.
-/

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsSepClosure K L]
  (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]

/-- An actual tame coefficient at exponent n is an nth root of unity. -/
theorem tameCoefficient_pow_eq_one
    (n : ℕ) (hn : IsUnit (n : A)) (σ : actualNormalizationInertiaGroup A K L Q) :
    tameCoefficient A K L Q n hn σ ^ n = 1 := by
  obtain ⟨E, hE⟩ := exists_actualFiniteStageTameOrder_multiple A K L Q n hn
  rw [tameCoefficient_eq_finite A K L Q n hn E hE σ, ← pow_mul, Nat.div_mul_cancel hE]
  exact congrArg Units.val ((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).property

/-- Original inertia attains a primitive root at every invertible exponent. -/
theorem exists_tameCoefficient_isPrimitiveRoot
    (n : ℕ) (hn : IsUnit (n : A)) :
    ∃ σ : actualNormalizationInertiaGroup A K L Q,
      IsPrimitiveRoot (tameCoefficient A K L Q n hn σ) n := by
  obtain ⟨E, hE⟩ := exists_actualFiniteStageTameOrder_multiple A K L Q n hn
  obtain ⟨ζ, hζ⟩ := actualFiniteStageTameOrder_exists_primitiveRoot A K L Q E
  have hm := actualFiniteStageTameOrder_pos A K L Q E
  let hu : IsUnit ζ := hζ.isUnit (Nat.ne_of_gt hm)
  let z : rootsOfUnity (actualFiniteStageTameOrder A K L Q E) Q.ResidueField :=
    ⟨hu.unit, by
      apply Units.ext
      change (hu.unit : Q.ResidueField) ^ actualFiniteStageTameOrder A K L Q E = 1
      rw [hu.unit_spec]
      exact hζ.pow_eq_one⟩
  obtain ⟨σ, hσ⟩ := actualFiniteTameCoordinate_surjective A K L Q E z
  have hs : (((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val).val = ζ :=
    (congrArg (fun r : rootsOfUnity (actualFiniteStageTameOrder A K L Q E) Q.ResidueField =>
      (r.val : Q.ResidueField)) hσ).trans hu.unit_spec
  refine ⟨σ, ?_⟩
  rw [tameCoefficient_eq_finite A K L Q n hn E hE σ, hs]
  exact IsPrimitiveRoot.pow hm hζ (Nat.div_mul_cancel hE).symm

/-- Triviality of every actual tame power detects exactly divisibility of its exponent. -/
theorem tameCoefficient_pow_trivial_iff_dvd
    (n : ℕ) (hn : IsUnit (n : A)) (r : ℕ) :
    (∀ σ : actualNormalizationInertiaGroup A K L Q,
      tameCoefficient A K L Q n hn σ ^ r = 1) ↔ n ∣ r := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := exists_tameCoefficient_isPrimitiveRoot A K L Q n hn
    exact (hσ.pow_eq_one_iff_dvd r).mp (h σ)
  · rintro ⟨k, rfl⟩ σ
    rw [pow_mul, tameCoefficient_pow_eq_one A K L Q n hn σ, one_pow]

end AnabelianGeometry.WeightFiltration
