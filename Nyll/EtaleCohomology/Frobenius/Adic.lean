/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Frobenius.ArithmeticComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.SchemePullback
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Actual pullback on classical rational ℓ-adic cohomology

The finite levels, coefficient reductions, inverse limit, and rationalization
are the existing classical étale cohomology constructions. Pullback is constructed
at these levels and then extended to the inverse limit and to `ℚ_[ℓ]`.

The finite-field operator is pullback by the base change of the original
q-power scheme Frobenius. Its equality with inverse arithmetic Frobenius is
proved using the existing finite-coefficient comparison. No point-count or
finiteness theorem is used in these constructions.

-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits EtaleFundamentalGroups.Cohomology

namespace EtaleCohomology.Classical

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Pullback on the original finite levels, with the prototype's argument order. -/
abbrev finiteLevelPullback (f : X ⟶ Y) (ℓ : ℕ) [Fact ℓ.Prime] (n i : ℕ) :
    finiteLevelCohomology Y ℓ n i →ₗ[ℤ_[ℓ]] finiteLevelCohomology X ℓ n i :=
  finiteLevelCohomologyPullback ℓ f n i

/-- Finite-level pullback commutes with the existing coefficient reductions. -/
theorem finiteLevelPullback_reduction (n i : ℕ)
    (x : finiteLevelCohomology Y ℓ (n + 1) i) :
    finiteLevelReduction X ℓ n i (finiteLevelPullback f ℓ (n + 1) i x) =
      finiteLevelPullback f ℓ n i (finiteLevelReduction Y ℓ n i x) :=
  (finiteLevelCohomologyPullback_reduction ℓ f n i x).symm

/-- The original integral pullback, with the prototype's argument order. -/
abbrev ellAdicPullback (f : X ⟶ Y) (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) :
    ellAdicCohomology Y ℓ i →ₗ[ℤ_[ℓ]] ellAdicCohomology X ℓ i :=
  ellAdicCohomologyPullback ℓ f i

/-- The original rational pullback, with the prototype's argument order. -/
abbrev rationalEllAdicPullback (f : X ⟶ Y) (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) :
    rationalEllAdicCohomology ℓ Y i →ₗ[ℚ_[ℓ]] rationalEllAdicCohomology ℓ X i :=
  rationalEllAdicCohomologyPullback ℓ f i

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] (C : Scheme.{u}) [C.Over (Spec (.of k))]

local notation "CΩ" => pullback (C ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

/-- Geometric Frobenius on the actual rational ℓ-adic cohomology. -/
def rationalEllAdicFrobenius (i : ℕ) :
    Module.End ℚ_[ℓ] (rationalEllAdicCohomology ℓ CΩ i) :=
  rationalEllAdicPullback (Scheme.constantBaseChangeFrobenius k Ω C) ℓ i

/-- The constructed operator has geometric, hence inverse arithmetic, orientation. -/
theorem rationalEllAdicFrobenius_eq_inverseArithmetic (i : ℕ) :
    rationalEllAdicFrobenius ℓ k Ω C i =
      rationalEllAdicPullback (Scheme.constantFieldTwist k Ω C
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm) ℓ i := by
  have h : ellAdicPullback (Scheme.constantBaseChangeFrobenius k Ω C) ℓ i =
      ellAdicPullback (Scheme.constantFieldTwist k Ω C
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm) ℓ i := by
    apply LinearMap.ext
    intro x
    apply ellAdicCohomology_ext CΩ ℓ i
    intro n
    exact geometricFrobenius_eq_inverseArithmetic_on_constantCohomology
      k Ω C (ellPowerCoefficients ℓ n) i (x.val n)
  exact congrArg (fun g => g.baseChange ℚ_[ℓ]) h

end EtaleCohomology.Classical
