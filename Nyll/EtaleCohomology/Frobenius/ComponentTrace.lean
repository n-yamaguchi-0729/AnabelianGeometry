/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ComponentCohomologyTrace
public import Nyll.EtaleCohomology.Frobenius.RationalAdic
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Trace

/-!
# Actual Frobenius powers on the original component cohomology

The original geometric Frobenius action on constant cohomology equals
the actual inverse arithmetic action. Every power is therefore the
pullback of an actual constant-field scheme isomorphism. Applying the
proved original component decomposition computes the trace from its
actual fixed-component blocks. No action on cohomology is supplied as
an extra input.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open EtaleCohomology.Classical

namespace EtaleCohomology

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]

local notation "XΩ" => (pullback (X ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) : Scheme)

/-- The actual inverse arithmetic scheme isomorphism for the indicated
power, on the literal geometric base change. -/
def inverseArithmeticFrobeniusPowerIso (m : ℕ) : XΩ ≅ XΩ :=
  Scheme.constantFieldTwistIso k Ω X
    ((FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm ^ m)

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The original Frobenius power acts by the pullback of the actual
inverse arithmetic power isomorphism. -/
theorem finiteFieldFrobeniusRationalEllAdicCohomology_pow_eq_iso (i m : ℕ) :
    (finiteFieldFrobeniusRationalEllAdicCohomology k Ω X ℓ i) ^ m =
      rationalEllAdicCohomologyPullback ℓ (inverseArithmeticFrobeniusPowerIso k Ω X m).hom i := by
  rw [finiteFieldFrobeniusRationalEllAdicCohomology_eq_inverseArithmetic]
  change (rationalEllAdicCohomologyPullback ℓ (Scheme.constantFieldTwist k Ω X
    (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm) i) ^ m =
      rationalEllAdicCohomologyPullback ℓ (Scheme.constantFieldTwist k Ω X
        ((FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm ^ m)) i
  induction m with
  | zero =>
      rw [pow_zero, pow_zero, Scheme.constantFieldTwist_one,
        rationalEllAdicCohomologyPullback_id]
  | succ m ih =>
      rw [pow_succ, pow_succ, Scheme.constantFieldTwist_mul,
        rationalEllAdicCohomologyPullback_comp_end, ih]

variable [IsNoetherian (pullback (X ↘ Spec (CommRingCat.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))]
  (hdom : ∀ x : (pullback (X ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) : Scheme.{u}),
    IsDomain ((pullback (X ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) : Scheme.{u}).presheaf.stalk x))

include hdom in
/-- Every original Frobenius power has trace supported on the actual
fixed components of its inverse arithmetic scheme action. -/
theorem finiteFieldFrobeniusRationalEllAdicCohomology_trace_components (i m : ℕ)
    [∀ Z : irreducibleComponents XΩ, FiniteDimensional ℚ_[ℓ]
      (rationalEllAdicCohomology ℓ ((XΩ).reducedIrreducibleComponent Z.1 Z.2) i)] :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ XΩ i)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k Ω X ℓ i) ^ m) =
      ∑ᶠ Z : {Z : irreducibleComponents XΩ //
          Scheme.irreducibleComponentsIsoEquiv (inverseArithmeticFrobeniusPowerIso k Ω X m) Z = Z},
        LinearMap.trace ℚ_[ℓ]
          (rationalEllAdicCohomology ℓ ((XΩ).reducedIrreducibleComponent Z.val.1 Z.val.2) i)
          (rationalEllAdicComponentDiagonal (inverseArithmeticFrobeniusPowerIso k Ω X m)
            ℓ i Z.val) := by
  rw [finiteFieldFrobeniusRationalEllAdicCohomology_pow_eq_iso]
  exact rationalEllAdicCohomology_trace_eq_sum_fixed_components
    (inverseArithmeticFrobeniusPowerIso k Ω X m) ℓ hdom i

end EtaleCohomology
