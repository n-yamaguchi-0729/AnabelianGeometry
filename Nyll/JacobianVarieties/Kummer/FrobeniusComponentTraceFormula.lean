/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
public import Nyll.AlgebraicCurves.Models.Divisors.CartierModulus
public import Nyll.AlgebraicCurves.Models.Divisors.FrobeniusComponentFixedCartierDegree
public import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivOfPoint
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Frobenius.ComponentTrace
public import Nyll.JacobianVarieties.Kummer.CurveLefschetzTrace
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentIsomorphism
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponents
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# The Lefschetz formula on a Frobenius-fixed geometric component

The actual fixed-point count equals the Cartier intersection degree.
Applying the curve trace formula to the same component and graph identifies
that degree with the alternating trace on its rational ℓ-adic cohomology.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open EtaleCohomology.Classical

namespace EtaleCohomology

private theorem natCast_eq_of_intDegree {R : Type*} [Ring R]
    (n : ℕ) (degree : ℤ) (trace : R) (hn : degree = (n : ℤ))
    (htrace : (degree : R) = trace) : (n : R) = trace := by
  calc
    (n : R) = (degree : R) := by rw [hn, Int.cast_natCast]
    _ = trace := htrace

private theorem pointCount_eq_alternatingTrace_of_degree
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} [IsIntegral C]
    (d : C ⟶ Spec (CommRingCat.of K)) [IsProper d] [SmoothOfRelativeDimension 1 d]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (v : C ⟶ C) (hv : v ≫ d = d)
    (hI : ((graphOver d (𝟙 C) (Category.id_comp d)).ker.comap
      (graphOver d v hv)).IsInvertible) (count : ℕ)
    (hcount :
      let _ : Algebra K C.functionField := (AlgebraicCurve.baseToFunctionField d).toAlgebra
      let M := AlgebraicCurve.literalCurveModel d
      (M.cartierModulus
        ((graphOver d (𝟙 C) (Category.id_comp d)).ker.comap (graphOver d v hv)) hI).degree =
        (count : ℤ)) :
    (count : ℚ_[ℓ]) =
      LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 0)
          (rationalEllAdicCohomologyPullback ℓ v 0) -
        LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 1)
          (rationalEllAdicCohomologyPullback ℓ v 1) +
        LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 2)
          (rationalEllAdicCohomologyPullback ℓ v 2) :=
  natCast_eq_of_intDegree count _ _ hcount
    (AlgebraicCurve.CurveModel.lefschetz_trace_formula d ℓ hℓ v hv hI)

variable (k K : Type u) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [IsProper (X ↘ Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))
  (m : ℕ) [NeZero m]

include hℓ in
/-- The number of Frobenius-fixed points on an actual fixed geometric component equals
its alternating rational ℓ-adic trace. -/
theorem fixedComponent_pointCount_eq_alternatingTrace
    (Z : irreducibleComponents
      (pullback (C := Scheme) (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)))
    (hZ : Scheme.irreducibleComponentsIsoEquiv
      (inverseArithmeticFrobeniusPowerIso k K X m) Z = Z) :
    let X_K := pullback (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)
    let C := X_K.reducedIrreducibleComponent Z.1 Z.2
    let d := X_K.reducedIrreducibleComponentι Z.1 Z.2 ≫
      pullback.snd (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)
    let v := Scheme.constantBaseChangeFrobeniusFixedComponent k K X m Z hZ
    let count : ℕ := Nat.card {s : Spec (CommRingCat.of K) ⟶ C //
      s ≫ d = 𝟙 _ ∧ s ≫ v = s}
    let trace : ℚ_[ℓ] :=
      LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 0)
          (rationalEllAdicCohomologyPullback ℓ v 0) -
        LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 1)
          (rationalEllAdicCohomologyPullback ℓ v 1) +
        LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 2)
          (rationalEllAdicCohomologyPullback ℓ v 2)
    (count : ℚ_[ℓ]) = trace := by
  intro X_K C d v count trace
  let g : X_K ⟶ Spec (CommRingCat.of K) :=
    pullback.snd (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)
  have : IsProper d := reducedIrreducibleComponent_isProper g Z
  have : SmoothOfRelativeDimension 1 d := reducedIrreducibleComponent_smooth_one g Z
  let hv := Scheme.constantBaseChangeFrobeniusFixedComponent_toBase k K X m Z hZ
  let I := (graphOver d (𝟙 C) (Category.id_comp d)).ker.comap (graphOver d v hv)
  have hI : I.IsInvertible :=
    Scheme.constantBaseChangeFrobenius_componentFixedIdeal_isInvertible k K X m Z hZ
  refine pointCount_eq_alternatingTrace_of_degree d ℓ hℓ v hv hI count ?_
  exact Scheme.constantBaseChangeFrobenius_componentFixedCartierModulus_degree_pointCount
    k K X m Z hZ

end EtaleCohomology
