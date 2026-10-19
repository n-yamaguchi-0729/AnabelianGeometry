/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteTameCofinality
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinateTower

/-!
# Tame coefficients at arbitrary invertible exponents

Finite tame coordinates reduce independently of the chosen finite stage.
Cofinality therefore gives an original inertia coefficient at every exponent
invertible in the base DVR.
-/

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]

/-- Reduced actual tame coefficients agree along actual finite normalization towers. -/
theorem finiteTameCoefficient_reduce_tower [IsGalois K L]
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F)
    (n : ℕ) (hn : n ∣ actualFiniteStageTameOrder A K L Q E)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    (((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val).val ^
        (actualFiniteStageTameOrder A K L Q E / n) =
      (((actualFiniteTameCoordinate A K L Q F).hom'.toFun σ).val).val ^
        (actualFiniteStageTameOrder A K L Q F / n) := by
  rw [actualFiniteTameCoordinate_tower A K L Q E F h σ, ← pow_mul,
    Nat.div_mul_div (actualFiniteStageTameOrder_dvd_of_le A K L Q E F h) hn]

/-- Reduction to a common exponent is independent of the finite Galois stage. -/
theorem finiteTameCoefficient_reduce_independent [IsGalois K L]
    (E F : FiniteGaloisIntermediateField K L) (n : ℕ)
    (hE : n ∣ actualFiniteStageTameOrder A K L Q E)
    (hF : n ∣ actualFiniteStageTameOrder A K L Q F)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    (((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val).val ^
        (actualFiniteStageTameOrder A K L Q E / n) =
      (((actualFiniteTameCoordinate A K L Q F).hom'.toFun σ).val).val ^
        (actualFiniteStageTameOrder A K L Q F / n) := by
  exact (finiteTameCoefficient_reduce_tower A K L Q E (E ⊔ F) le_sup_left n hE σ).trans
    (finiteTameCoefficient_reduce_tower A K L Q F (E ⊔ F) le_sup_right n hF σ).symm

/-- The original tame coefficient at an arbitrary exponent invertible in the base. -/
def tameCoefficient [IsSepClosure K L]
    (n : ℕ) (hn : IsUnit (n : A)) (σ : actualNormalizationInertiaGroup A K L Q) :
    Q.ResidueField :=
  let E := Classical.choose (exists_actualFiniteStageTameOrder_multiple A K L Q n hn)
  (((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val).val ^
    (actualFiniteStageTameOrder A K L Q E / n)

/-- Any actual finite stage of divisible tame order computes the same tame coefficient. -/
theorem tameCoefficient_eq_finite [IsSepClosure K L]
    (n : ℕ) (hn : IsUnit (n : A)) (E : FiniteGaloisIntermediateField K L)
    (hE : n ∣ actualFiniteStageTameOrder A K L Q E)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    tameCoefficient A K L Q n hn σ =
      (((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val).val ^
        (actualFiniteStageTameOrder A K L Q E / n) := by
  exact finiteTameCoefficient_reduce_independent A K L Q _ E n
    (Classical.choose_spec (exists_actualFiniteStageTameOrder_multiple A K L Q n hn)) hE σ

end AnabelianGeometry.WeightFiltration
