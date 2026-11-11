/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Divisors.CartierModulus
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.EffectiveCartierIdeal
public import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivOfPoint
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.CartierAdicCyclePullback
public import Nyll.EtaleCohomology.Classical.GraphAdicCycleClass
public import Nyll.EtaleCohomology.Classical.GraphCartierCycleClass
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalGraphEdges
public import Nyll.JacobianVarieties.Kummer.CurveCartierCycleDegree
public import Nyll.JacobianVarieties.Kummer.CurveDiagonalEdgeClass
public import Nyll.JacobianVarieties.Kummer.CurveNativeAdicH2
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.LinearAlgebra.Trace

/-!
# Native degree of an actual graph–diagonal intersection

When the original inverse-image ideal is Cartier, its full multiplicity
degree is the native degree of the original diagonal pulled back by the
actual graph. Subtracting the two native edge classes computes the same
graph degree for the normalized diagonal.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth
  selfProduct_isIntegral

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The trace on the original one-dimensional H² is the native degree
of the image of its canonical degree-one class. -/
theorem nativeRationalEllAdicH2_trace
    (A : Module.End ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 2)) :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 2) A =
      M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        (A ((M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm 1)) := by
  have : FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 2) :=
    M.nativeRationalEllAdicH2_finiteDimensional ℓ hℓ
  let e := M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
  have hA : A = e.toLinearMap.smulRight (A (e.symm 1)) := by
    apply LinearMap.ext
    intro x
    have hx : x = e x • e.symm 1 := by
      apply e.injective
      rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
    exact (congrArg A hx).trans (A.map_smul (e x) (e.symm 1))
  exact (congrArg (LinearMap.trace ℚ_[ℓ]
    (rationalEllAdicCohomology ℓ M.C 2)) hA).trans
      (LinearMap.trace_smulRight e.toLinearMap (A (e.symm 1)))

variable (v : M.C ⟶ M.C) (hv : v ≫ M.toBase = M.toBase)

local notation "Γ" => graphOver M.toBase v hv
local notation "I" =>
  (AlgebraicGeometry.Scheme.IdealSheafData.comap (AlgebraicGeometry.Scheme.Hom.ker (graphOver
    M.toBase (𝟙 M.C) (Category.id_comp M.toBase)))) Γ

/-- Original graph pullback of the diagonal has the full degree of
the original graph–diagonal Cartier ideal. -/
theorem nativeRationalDiagonalCycleClass_graph_degree (hI : (I).IsInvertible) :
    M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        (rationalEllAdicCohomologyPullback ℓ Γ 2
          (rationalGraphCycleClass M.toBase M.toBase (𝟙 M.C)
            (Category.id_comp M.toBase) ℓ hℓ)) =
      ((M.cartierModulus I hI).degree : ℚ_[ℓ]) := by
  have hc : Γ ≫ (pullback.snd M.toBase M.toBase ≫ M.toBase) = M.toBase := by
    rw [← Category.assoc, graphOver_snd, Category.id_comp]
  have h := rationalEffectiveCartierCycleClass_pullback Γ
    (pullback.snd M.toBase M.toBase ≫ M.toBase) ℓ hℓ
    (graphEffectiveCartierDivisor M.toBase M.toBase (𝟙 M.C)
      (Category.id_comp M.toBase)) hI.isEffectiveCartier
  rw [hc] at h
  exact (congrArg (M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ) h).trans
    (M.nativeRationalEllAdicH2DegreeEquiv_cartier ℓ hℓ I hI)

/-- Removing the two original edge classes subtracts the actual
pullback degree in H² and one from the same intersection degree. -/
theorem nativeRationalDiagonalMiddleClass_graph_degree (hI : (I).IsInvertible) :
    M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        (rationalEllAdicCohomologyPullback ℓ Γ 2
          (M.nativeRationalDiagonalMiddleClass ℓ hℓ)) =
      ((M.cartierModulus I hI).degree : ℚ_[ℓ]) -
        M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
          (rationalEllAdicCohomologyPullback ℓ v 2
            ((M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm 1)) - 1 := by
  rw [nativeRationalDiagonalMiddleClass, map_sub, map_sub,
    M.nativeRationalDiagonalCycleClass_graph_degree ℓ hℓ v hv hI,
    rationalEllAdicEdgeMap_graphOver, map_add, LinearEquiv.apply_symm_apply,
    sub_add_eq_sub_sub]

end AlgebraicCurve.CurveModel
