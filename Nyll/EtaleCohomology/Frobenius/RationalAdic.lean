/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Frobenius.ArithmeticComparison
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Frobenius on classical rational ℓ-adic cohomology

The original base-changed q-power scheme Frobenius acts on the original
integral compatible families and their original rational scalar extensions.
Every finite projection and every power retains the corresponding finite
coefficient map. The existing geometric/arithmetic site comparison gives
the equality with inverse arithmetic Frobenius on these same objects.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

namespace EtaleCohomology

open EtaleCohomology.Classical

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  (ℓ : ℕ) [Fact ℓ.Prime]

local notation "XΩ" => pullback (X ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

/-- Actual scheme Frobenius acts on the existing integral classical
ℓ-adic cohomology. -/
def finiteFieldFrobeniusEllAdicCohomology (i : ℕ) :
    Module.End ℤ_[ℓ] (ellAdicCohomology XΩ ℓ i) :=
  ellAdicCohomologyPullback ℓ (Scheme.constantBaseChangeFrobenius k Ω X) i

/-- Actual scheme Frobenius acts on the standard classical rational
ℓ-adic cohomology, by scalar extension of the original integral action. -/
def finiteFieldFrobeniusRationalEllAdicCohomology (i : ℕ) :
    Module.End ℚ_[ℓ] (rationalEllAdicCohomology ℓ XΩ i) :=
  rationalEllAdicCohomologyPullback ℓ (Scheme.constantBaseChangeFrobenius k Ω X) i

/-- Every original finite projection intertwines every Frobenius power. -/
theorem finiteFieldFrobeniusEllAdicCohomology_projection_pow (i n m : ℕ)
    (a : ellAdicCohomology XΩ ℓ i) :
    ellAdicProjection XΩ ℓ i n (((finiteFieldFrobeniusEllAdicCohomology k Ω X ℓ i) ^ m) a) =
      ((finiteLevelCohomologyPullback ℓ
        (Scheme.constantBaseChangeFrobenius k Ω X) n i) ^ m)
          (ellAdicProjection XΩ ℓ i n a) :=
  ellAdicProjection_pullback_pow ℓ (Scheme.constantBaseChangeFrobenius k Ω X) i n m a

/-- Rational Frobenius powers act on pure tensors through the same
original integral Frobenius powers. -/
theorem finiteFieldFrobeniusRationalEllAdicCohomology_pow_tmul
    (i m : ℕ) (q : ℚ_[ℓ]) (a : ellAdicCohomology XΩ ℓ i) :
    ((finiteFieldFrobeniusRationalEllAdicCohomology k Ω X ℓ i) ^ m)
        (q ⊗ₜ[ℤ_[ℓ]] a) =
      q ⊗ₜ[ℤ_[ℓ]] ((finiteFieldFrobeniusEllAdicCohomology k Ω X ℓ i) ^ m) a :=
  rationalEllAdicCohomologyPullback_pow_tmul ℓ
    (Scheme.constantBaseChangeFrobenius k Ω X) i m q a

/-- All rational Frobenius powers are pullbacks by the actual original
scheme Frobenius powers, with no separate supplied action. -/
theorem finiteFieldFrobeniusRationalEllAdicCohomology_pow (i m : ℕ) :
    (finiteFieldFrobeniusRationalEllAdicCohomology k Ω X ℓ i) ^ m =
      rationalEllAdicCohomologyPullback ℓ
        ((End.of (Scheme.constantBaseChangeFrobenius k Ω X)) ^ m).asHom i :=
  rationalEllAdicCohomologyPullback_pow ℓ (Scheme.constantBaseChangeFrobenius k Ω X) i m

/-- The geometric/arithmetic equality at actual finite coefficients
passes to the same integral inverse limit. -/
theorem finiteFieldFrobeniusEllAdicCohomology_eq_inverseArithmetic (i : ℕ) :
    finiteFieldFrobeniusEllAdicCohomology k Ω X ℓ i =
      ellAdicCohomologyPullback ℓ (Scheme.constantFieldTwist k Ω X
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm) i := by
  apply LinearMap.ext
  intro a
  apply ellAdicCohomology_ext XΩ ℓ i
  intro n
  exact geometricFrobenius_eq_inverseArithmetic_on_constantCohomology k Ω X
    (ellPowerCoefficients ℓ n) i (a.val n)

/-- Scalar extension retains the actual inverse-arithmetic comparison. -/
theorem finiteFieldFrobeniusRationalEllAdicCohomology_eq_inverseArithmetic (i : ℕ) :
    finiteFieldFrobeniusRationalEllAdicCohomology k Ω X ℓ i =
      rationalEllAdicCohomologyPullback ℓ (Scheme.constantFieldTwist k Ω X
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm) i :=
  congrArg (fun t : Module.End ℤ_[ℓ] (ellAdicCohomology XΩ ℓ i) =>
    t.baseChange ℚ_[ℓ])
      (finiteFieldFrobeniusEllAdicCohomology_eq_inverseArithmetic k Ω X ℓ i)

/-- Every rational Frobenius power has the original inverse-arithmetic
power action on the same classical rational cohomology. -/
theorem finiteFieldFrobeniusRationalEllAdicCohomology_pow_eq_inverseArithmetic
    (i m : ℕ) :
    (finiteFieldFrobeniusRationalEllAdicCohomology k Ω X ℓ i) ^ m =
      (rationalEllAdicCohomologyPullback ℓ (Scheme.constantFieldTwist k Ω X
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm) i) ^ m :=
  congrArg (fun t : Module.End ℚ_[ℓ] (rationalEllAdicCohomology ℓ XΩ i) => t ^ m)
    (finiteFieldFrobeniusRationalEllAdicCohomology_eq_inverseArithmetic k Ω X ℓ i)

end EtaleCohomology
