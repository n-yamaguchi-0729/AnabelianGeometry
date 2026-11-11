/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.AlgebraicCurves.Models.Divisors.FrobeniusFixedCartierDegree
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Frobenius.ComponentTrace
public import Nyll.EtaleCohomology.Frobenius.RationalAdic
public import Nyll.EtaleCohomology.Frobenius.RationalAdicH0Trace
public import Nyll.JacobianVarieties.Kummer.FrobeniusComponentTraceSum
public import Nyll.JacobianVarieties.Kummer.SmoothProperCurveH2Frobenius
public import Nyll.JacobianVarieties.Kummer.SmoothProperGeometricComponentTrace
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentIsomorphism
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChangePoints
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponentPointCount
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponents
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.FiniteIntermediateFieldDegree
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.LinearAlgebra.Trace

/-!
# The Qℓ Lefschetz trace formula for smooth proper curves

Let `X` be a smooth proper curve over a finite field `k`, let `K` be an
algebraic closure, and let `ℓ` be invertible in `K`. Write `X_K = X ×_k K`
and let `k_m` be the degree-`m` extension of `k` inside `K`. For `m > 0`,
`lefschetz_trace_formula_curve` proves

`#X(k_m) = Tr(Frob^m | H⁰) - Tr(Frob^m | H¹) + Tr(Frob^m | H²)`,

where `Hⁱ = Hⁱ(X_K, ℚℓ)`. The operator
`finiteFieldFrobeniusRationalEllAdicCohomology` is induced by the base
change of the `#k`-power scheme Frobenius. Its equality with inverse
arithmetic Frobenius is proved in `Frobenius.RationalAdic`.

No geometric connectedness or nonemptiness assumption is needed. The
proof sums the graph--diagonal intersection formula over the geometric
components fixed by Frobenius. The geometrically connected formula is a
corollary: the outer traces are `1` and `(#k)^m`.

See [Milne, *Lectures on Étale Cohomology*, §25](https://www.jmilne.org/math/CourseNotes/LEC.pdf)
and the
[Stacks Project, The Trace Formula](https://stacks.math.columbia.edu/tag/03TW).
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

include hℓ in
/-- For a smooth proper curve over a finite field, the number of points
over the degree-`m` extension is the alternating trace of `Frob^m` on its
geometric rational étale cohomology. Disconnected and empty curves are included. -/
theorem lefschetz_trace_formula_curve :
    let kₘ := LocalClassFieldTheory.finiteResidueGaloisIntermediateFieldIn k K m
    (Nat.card (SchemeHomOver (Spec.algebraMap k kₘ)
      (X ↘ Spec (CommRingCat.of k))) : ℚ_[ℓ]) =
      LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ (Y) 0)
          ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 0) ^ m) -
        LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ (Y) 1)
          ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 1) ^ m) +
        LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ (Y) 2)
          ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 2) ^ m) := by
  intro kₘ
  exact (finiteFieldPointCount_eq_fixedComponentAlternatingTraceSum k K X ℓ hℓ m).trans
    (smoothProperCurveFrobeniusAlternatingTrace_eq_fixedSum k K X ℓ hℓ m).symm

include hℓ in
/-- For a geometrically connected curve, the outer traces in the
Lefschetz formula are `1` and `(#k)^m`. -/
theorem lefschetz_trace_formula_geometricallyConnected_curve
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k))] :
    let kₘ := LocalClassFieldTheory.finiteResidueGaloisIntermediateFieldIn k K m
    (Nat.card (SchemeHomOver (Spec.algebraMap k kₘ)
      (X ↘ Spec (CommRingCat.of k))) : ℚ_[ℓ]) =
      1 - LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ (Y) 1)
          ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 1) ^ m) +
        (Fintype.card k : ℚ_[ℓ]) ^ m := by
  intro kₘ
  have : IsIntegral (Y) := Scheme.constantBaseChange_smoothProperCurve_isIntegral k K X
  exact (lefschetz_trace_formula_curve k K X ℓ hℓ m).trans
    (congrArg₂
      (fun a b : ℚ_[ℓ] => a - LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ (Y) 1)
          ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 1) ^ m) + b)
      (trace_rationalEllAdicH0_frobenius_pow k K X ℓ m)
      (trace_rationalEllAdicH2_frobenius_pow k K X ℓ hℓ m))

end EtaleCohomology
