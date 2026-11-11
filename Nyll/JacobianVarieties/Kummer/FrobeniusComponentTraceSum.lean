/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Frobenius.ComponentTrace
public import Nyll.EtaleCohomology.Frobenius.RationalAdic
public import Nyll.JacobianVarieties.Kummer.FrobeniusComponentTraceFormula
public import Nyll.JacobianVarieties.Kummer.SmoothProperGeometricComponentTrace
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentIsomorphism
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponentPointCount
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponents
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.FiniteIntermediateFieldDegree
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.LinearAlgebra.Trace

/-!
# Point counts and alternating traces summed over fixed components

The point count and the alternating trace agree on each actual fixed
geometric component. Summing the pointwise equalities gives the equality
between the two component contributions to the global trace formula.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace NeronModelInfra
open EtaleCohomology.Classical

namespace EtaleCohomology

variable (k K : Type u) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [IsProper (X ↘ Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))
  (m : ℕ) [NeZero m]

local notation "Y" => pullback (C := Scheme)
  (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)
local notation "g" => pullback.snd (C := Scheme)
  (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)
local notation "Fixed" => {Z : irreducibleComponents Y //
  Scheme.irreducibleComponentsIsoEquiv (inverseArithmeticFrobeniusPowerIso k K X m) Z = Z}

include hℓ in
/-- Summing the actual component point counts gives the sum of the same component traces. -/
theorem fixedComponent_pointCountSum_eq_alternatingTraceSum :
    (∑ᶠ Z : Fixed,
      (Nat.card {s : Spec (CommRingCat.of K) ⟶ (Y).reducedIrreducibleComponent Z.val.1 Z.val.2 //
        s ≫ ((Y).reducedIrreducibleComponentι Z.val.1 Z.val.2 ≫ g) = 𝟙 _ ∧
          s ≫ Scheme.constantBaseChangeFrobeniusFixedComponent k K X m Z.val Z.property = s} :
        ℚ_[ℓ])) =
      ∑ᶠ Z : Fixed,
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
  apply congrArg (fun f : Fixed → ℚ_[ℓ] => ∑ᶠ Z, f Z)
  funext Z
  exact fixedComponent_pointCount_eq_alternatingTrace k K X ℓ hℓ m Z.val Z.property

private theorem cast_count_eq_trace_sum {R : Type*} [AddCommMonoidWithOne R]
    {ι : Type*} [Finite ι] {n : ℕ} {f : ι → ℕ} {t : R}
    (hn : n = ∑ᶠ i, f i) (ht : (∑ᶠ i, (f i : R)) = t) : (n : R) = t := by
  calc
    (n : R) = ((∑ᶠ i, f i : ℕ) : R) := congrArg (fun x : ℕ => (x : R)) hn
    _ = ∑ᶠ i, (f i : R) := Nat.cast_finsum f
    _ = t := ht

/-- The sum of the alternating traces of the actual Frobenius-fixed components. -/
noncomputable abbrev frobeniusFixedComponentAlternatingTraceSum : ℚ_[ℓ] :=
      ∑ᶠ Z : Fixed,
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
              (Scheme.constantBaseChangeFrobeniusFixedComponent k K X m Z.val Z.property) 2))

omit [NeZero m] in
include hℓ in
/-- The alternating trace on the whole curve equals the sum on its fixed components. -/
theorem smoothProperCurveFrobeniusAlternatingTrace_eq_fixedSum :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ (Y) 0)
          ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 0) ^ m) -
        LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ (Y) 1)
          ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 1) ^ m) +
        LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ (Y) 2)
          ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 2) ^ m) =
      frobeniusFixedComponentAlternatingTraceSum k K X ℓ m :=
  SmoothProperCurve.nativeFrobeniusRationalCohomology_alternatingTrace_geometricComponents
    k K X ℓ hℓ m

include hℓ in
/-- The original extension-field point count is the sum of the alternating traces
of the fixed geometric components. -/
theorem finiteFieldPointCount_eq_fixedComponentAlternatingTraceSum :
    let kₘ := LocalClassFieldTheory.finiteResidueGaloisIntermediateFieldIn k K m
    let pointCount : ℕ := Nat.card (SchemeHomOver (Spec.algebraMap k kₘ)
      (X ↘ Spec (CommRingCat.of k)))
    (pointCount : ℚ_[ℓ]) =
      frobeniusFixedComponentAlternatingTraceSum k K X ℓ m := by
  intro kₘ pointCount
  classical
  let X_K := pullback (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (CommRingCat.of k))
  have : IsNoetherian X_K := smoothProperScheme_isNoetherian g
  let : Fintype (irreducibleComponents X_K) := smoothProperComponentsFintype g
  let count (Z : Fixed) : ℕ :=
    Nat.card {s : Spec (CommRingCat.of K) ⟶ X_K.reducedIrreducibleComponent Z.val.1 Z.val.2 //
      s ≫ (X_K.reducedIrreducibleComponentι Z.val.1 Z.val.2 ≫ g) = 𝟙 _ ∧
        s ≫ Scheme.constantBaseChangeFrobeniusFixedComponent k K X m Z.val Z.property = s}
  have hcount : pointCount = ∑ᶠ Z : Fixed, count Z := by
    as_aux_lemma =>
      exact @id (pointCount = ∑ᶠ Z : Fixed, count Z)
        (finiteFieldPointCount_eq_sum_fixedComponents k K X m (smoothSchemeDomainStalks g))
  have hsum := fixedComponent_pointCountSum_eq_alternatingTraceSum k K X ℓ hℓ m
  exact cast_count_eq_trace_sum (f := count) hcount hsum

end EtaleCohomology
