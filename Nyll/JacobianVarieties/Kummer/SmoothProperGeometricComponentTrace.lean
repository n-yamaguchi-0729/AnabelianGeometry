/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.EtaleCohomology.Frobenius.ComponentH0Trace
public import Nyll.EtaleCohomology.Frobenius.GeometricComponentTrace
public import Nyll.JacobianVarieties.Kummer.SmoothProperComponentCohomology
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponents
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# Geometric component traces of the original finite-field curve

The literal geometric base change supplies its actual finite component
decomposition and the finite-dimensional original component groups.
The original Frobenius traces in degrees zero, one, and two therefore
sum over its actual geometric restrictions to the fixed components.
The same calculation gives the three-term alternating trace, including
the empty curve. Its degree-zero term counts the actual fixed components.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicGeometry.SmoothProperCurve

private theorem alternating_eq_finsum {I A : Type*} [Finite I] [AddCommGroup A]
    (a b c : I → A) {x y z : A}
    (hx : x = ∑ᶠ j, a j) (hy : y = ∑ᶠ j, b j) (hz : z = ∑ᶠ j, c j) :
    x - y + z = ∑ᶠ j, (a j - b j + c j) := by
  let _ : Fintype I := Fintype.ofFinite I
  rw [hx, hy, hz]
  simp only [finsum_eq_sum_of_fintype, Finset.sum_sub_distrib, Finset.sum_add_distrib]

variable (k K : Type u) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k))]
  [IsProper (X ↘ Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))]
  (ℓ : ℕ) [Fact ℓ.Prime]

local notation "Y" => pullback (C := Scheme) (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)
local notation "g" => pullback.snd (C := Scheme) (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)

omit [IsAlgClosed K] in
/-- The original H0 Frobenius trace counts components whose actual
subsets are fixed by geometric Frobenius itself. -/
theorem nativeFrobeniusRationalH0_trace_eq_geometricComponentCard (m : ℕ) :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y 0)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 0) ^ m) =
      (Nat.card {Z : irreducibleComponents Y //
        ((End.of (Scheme.constantBaseChangeFrobenius k K X)) ^ m).asHom '' Z.1 = Z.1} :
          ℚ_[ℓ]) := by
  let _ : IsNoetherian Y := smoothProperScheme_isNoetherian g
  have h := finiteFieldFrobeniusRationalH0_trace_eq_geometricComponentCard k K X ℓ
    (smoothSchemeDomainStalks g) m
  exact h

variable (hℓ : IsUnit (ℓ : K))

include hℓ in
/-- Each original trace in the curve formula is the sum of the
original traces of the actual geometric component endomorphisms. -/
theorem nativeFrobeniusRationalCohomology_trace_geometricComponents
    (i m : ℕ) (hi : i ≤ 2) :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y i)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ i) ^ m) =
      ∑ᶠ Z : {Z : irreducibleComponents Y //
          Scheme.irreducibleComponentsIsoEquiv (inverseArithmeticFrobeniusPowerIso k K X m) Z = Z},
        LinearMap.trace ℚ_[ℓ]
          (rationalEllAdicCohomology ℓ ((Y).reducedIrreducibleComponent Z.val.1 Z.val.2) i)
          (rationalEllAdicCohomologyPullback ℓ
            (Scheme.constantBaseChangeFrobeniusFixedComponent k K X m Z.val Z.property) i) := by
  let _ : IsNoetherian Y := smoothProperScheme_isNoetherian g
  let _ : ∀ Z : irreducibleComponents Y, FiniteDimensional ℚ_[ℓ]
      (rationalEllAdicCohomology ℓ ((Y).reducedIrreducibleComponent Z.1 Z.2) i) :=
    nativeRationalComponent_finiteDimensional_of_le_two K g ℓ hℓ i hi
  have h := finiteFieldFrobeniusRationalEllAdicCohomology_trace_geometricComponents k K X ℓ
    (smoothSchemeDomainStalks g) i m
  exact h

include hℓ in
/-- The actual three-term alternating trace on the original curve
is the sum of the same three-term traces on its actual fixed components. -/
theorem nativeFrobeniusRationalCohomology_alternatingTrace_geometricComponents (m : ℕ) :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y 0)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 0) ^ m) -
      LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y 1)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 1) ^ m) +
      LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y 2)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 2) ^ m) =
      ∑ᶠ Z : {Z : irreducibleComponents Y //
          Scheme.irreducibleComponentsIsoEquiv (inverseArithmeticFrobeniusPowerIso k K X m) Z = Z},
        (LinearMap.trace ℚ_[ℓ]
            (rationalEllAdicCohomology ℓ ((Y).reducedIrreducibleComponent Z.val.1 Z.val.2) 0)
            (rationalEllAdicCohomologyPullback ℓ
              (Scheme.constantBaseChangeFrobeniusFixedComponent k K X m Z.val Z.property) 0) -
          LinearMap.trace ℚ_[ℓ]
            (rationalEllAdicCohomology ℓ ((Y).reducedIrreducibleComponent Z.val.1 Z.val.2) 1)
            (rationalEllAdicCohomologyPullback ℓ
              (Scheme.constantBaseChangeFrobeniusFixedComponent k K X m Z.val Z.property) 1) +
          LinearMap.trace ℚ_[ℓ]
            (rationalEllAdicCohomology ℓ ((Y).reducedIrreducibleComponent Z.val.1 Z.val.2) 2)
            (rationalEllAdicCohomologyPullback ℓ
              (Scheme.constantBaseChangeFrobeniusFixedComponent k K X m Z.val Z.property) 2)) := by
  classical
  let I := {Z : irreducibleComponents Y //
    Scheme.irreducibleComponentsIsoEquiv (inverseArithmeticFrobeniusPowerIso k K X m) Z = Z}
  let _ : Fintype (irreducibleComponents Y) := smoothProperComponentsFintype g
  let _ : Fintype I := Fintype.ofFinite I
  let tr (i : ℕ) (Z : I) : ℚ_[ℓ] :=
    LinearMap.trace ℚ_[ℓ]
      (rationalEllAdicCohomology ℓ ((Y).reducedIrreducibleComponent Z.val.1 Z.val.2) i)
      (rationalEllAdicCohomologyPullback ℓ
        (Scheme.constantBaseChangeFrobeniusFixedComponent k K X m Z.val Z.property) i)
  have h0 := nativeFrobeniusRationalCohomology_trace_geometricComponents k K X ℓ hℓ 0 m
    (Nat.zero_le 2)
  have h1 := nativeFrobeniusRationalCohomology_trace_geometricComponents k K X ℓ hℓ 1 m
    (Nat.le_succ 1)
  have h2 := nativeFrobeniusRationalCohomology_trace_geometricComponents k K X ℓ hℓ 2 m le_rfl
  exact alternating_eq_finsum (tr 0) (tr 1) (tr 2) h0 h1 h2

end AlgebraicGeometry.SmoothProperCurve
