/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
public import Nyll.AlgebraicCurves.Models.Divisors.CartierModulus
public import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivOfPoint
public import Nyll.EtaleCohomology.Classical.AdicH0Comparison
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalKunnethMap
public import Nyll.JacobianVarieties.Kummer.CurveDiagonalEdgeClass
public import Nyll.JacobianVarieties.Kummer.CurveDiagonalMiddleTensor
public import Nyll.JacobianVarieties.Kummer.CurveGraphCycleDegree
public import Nyll.JacobianVarieties.Kummer.CurveNativeAdicH2
public import Nyll.JacobianVarieties.Kummer.CurveTensorTrace
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Tactic.Ring

/-!
# The Lefschetz trace formula for a curve endomorphism

For a smooth proper integral curve `C` over an algebraically closed field,
let `v : C ⟶ C` be an endomorphism over the base. If its graph meets the
diagonal in a Cartier divisor, `lefschetz_trace_formula` proves

`deg(Γ_v ⋅ Δ) = Tr(v* | H⁰) - Tr(v* | H¹) + Tr(v* | H²)`.

Here `Hⁱ` is `rationalEllAdicCohomology ℓ C i`. The intersection ideal is
the inverse image of the diagonal ideal along `graphOver c v hv`;
`cartierModulus` retains all of its stalk multiplicities. The algebra and
curve model introduced in the statements are constructed from `c`.

The proof identifies the middle component of the diagonal with the tensor
of `-id`, then evaluates its graph pullback as `-Tr(v* | H¹)`. The outer
components give the traces on `H⁰` and `H²`.

See [Milne, *Lectures on Étale Cohomology*, §25](https://www.jmilne.org/math/CourseNotes/LEC.pdf)
for the Lefschetz formula.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth
  selfProduct_isIntegral

private theorem nativeTensor_graph_degree_of_scheme_eq
    {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))
    {C : Scheme.{u}} (hC : M.C = C)
    {S : Scheme.{u}} (b : C ⟶ S) (v : C ⟶ C) (hv : v ≫ b = b) :
    let degree : rationalEllAdicCohomology ℓ C 2 → ℚ_[ℓ] :=
      hC ▸ (M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ :
        rationalEllAdicCohomology ℓ M.C 2 → ℚ_[ℓ])
    let tensor : TensorProduct ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 1)
        (rationalEllAdicCohomology ℓ C 1) :=
      hC ▸ M.nativeRationalH1NegativeIdentityTensor ℓ hℓ
    degree (rationalEllAdicCohomologyPullback ℓ (graphOver b v hv) 2
      (rationalEllAdicKunnethComponent ℓ b b 1 1 2 rfl tensor)) =
      -LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 1)
        (rationalEllAdicCohomologyPullback ℓ v 1) := by
  cases hC
  exact M.nativeRationalH1NegativeIdentityTensor_graph_degree_over ℓ hℓ b v hv

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} [IsIntegral C]
  (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))
  (v : C ⟶ C) (hv : v ≫ c = c)

/-- Literal evaluation of the canonical tensor on a graph. -/
private theorem literal_negativeIdentityTensor_graph_degree :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    let M := literalCurveModel c
    M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        (rationalEllAdicCohomologyPullback ℓ (graphOver c v hv) 2
          (rationalEllAdicKunnethComponent ℓ c c 1 1 2 rfl
            (M.nativeRationalH1NegativeIdentityTensor ℓ hℓ))) =
      -LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 1)
        (rationalEllAdicCohomologyPullback ℓ v 1) := by
  intro alg M
  exact nativeTensor_graph_degree_of_scheme_eq M ℓ hℓ (C := C) (rfl : M.C = C) c v hv

/-- The normalized diagonal contributes minus the trace on H¹. -/
theorem nativeRationalDiagonalMiddleClass_graph_trace :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    let M := literalCurveModel c
    M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        (rationalEllAdicCohomologyPullback ℓ (graphOver c v hv) 2
          (M.nativeRationalDiagonalMiddleClass ℓ hℓ)) =
      -LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 1)
        (rationalEllAdicCohomologyPullback ℓ v 1) := by
  intro alg M
  let degree (a : rationalEllAdicCohomology ℓ (pullback c c) 2) : ℚ_[ℓ] :=
    M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
      (rationalEllAdicCohomologyPullback ℓ (graphOver c v hv) 2 a)
  let x : ℚ_[ℓ] := degree (M.nativeRationalDiagonalMiddleClass ℓ hℓ)
  let y : ℚ_[ℓ] := degree (rationalEllAdicKunnethComponent ℓ c c 1 1 2 rfl
    (M.nativeRationalH1NegativeIdentityTensor ℓ hℓ))
  let z : ℚ_[ℓ] := -LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 1)
    (rationalEllAdicCohomologyPullback ℓ v 1)
  have hMiddle : x = y := by
    as_aux_lemma =>
      exact @id (x = y)
        (nativeRationalDiagonalMiddleClass_map_eq_negativeIdentityTensor c ℓ hℓ degree)
  have hTensor : y = z := by
    as_aux_lemma =>
      exact @id (y = z)
        (literal_negativeIdentityTensor_graph_degree c ℓ hℓ v hv)
  refine @Eq.trans ℚ_[ℓ] _ y _ ?_ ?_
  · exact hMiddle
  · exact hTensor

include hℓ in
/-- The graph--diagonal intersection number is the alternating trace of
`v*` on `H⁰`, `H¹`, and `H²`. The Cartier hypothesis is imposed on the
actual intersection ideal, so its degree includes all multiplicities. -/
theorem lefschetz_trace_formula
    (hI : ((graphOver c (𝟙 C) (Category.id_comp c)).ker.comap
      (graphOver c v hv)).IsInvertible) :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    let M := literalCurveModel c
    ((M.cartierModulus
        ((graphOver c (𝟙 C) (Category.id_comp c)).ker.comap (graphOver c v hv)) hI).degree :
      ℚ_[ℓ]) =
      LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 0)
          (rationalEllAdicCohomologyPullback ℓ v 0) -
        LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 1)
          (rationalEllAdicCohomologyPullback ℓ v 1) +
        LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 2)
          (rationalEllAdicCohomologyPullback ℓ v 2) := by
  intro alg M
  let I : C.IdealSheafData :=
    (graphOver c (𝟙 C) (Category.id_comp c)).ker.comap (graphOver c v hv)
  have : FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 0) :=
    finiteDimensional_rationalEllAdicH0 C ℓ
  have hzero : LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 0)
      (rationalEllAdicCohomologyPullback ℓ v 0) = 1 := by
    rw [rationalEllAdicCohomologyPullback_zero, LinearMap.trace_one,
      finrank_rationalEllAdicH0, Nat.cast_one]
  have hmiddle :
      -LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 1)
          (rationalEllAdicCohomologyPullback ℓ v 1) =
        ((M.cartierModulus I hI).degree : ℚ_[ℓ]) -
          M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
            (rationalEllAdicCohomologyPullback ℓ v 2
              ((M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm 1)) - 1 :=
    (nativeRationalDiagonalMiddleClass_graph_trace c ℓ hℓ v hv).symm.trans
      (M.nativeRationalDiagonalMiddleClass_graph_degree ℓ hℓ v hv hI)
  have htwo : LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ C 2)
      (rationalEllAdicCohomologyPullback ℓ v 2) =
        M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
          (rationalEllAdicCohomologyPullback ℓ v 2
            ((M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm 1)) :=
    M.nativeRationalEllAdicH2_trace ℓ hℓ (rationalEllAdicCohomologyPullback ℓ v 2)
  rw [hzero, htwo]
  calc
    ((M.cartierModulus I hI).degree : ℚ_[ℓ]) =
        (((M.cartierModulus I hI).degree : ℚ_[ℓ]) -
          M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
            (rationalEllAdicCohomologyPullback ℓ v 2
              ((M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm 1)) - 1) + 1 +
          M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
            (rationalEllAdicCohomologyPullback ℓ v 2
              ((M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm 1)) := by ring
    _ = _ := by rw [← hmiddle]; ring

end AlgebraicCurve.CurveModel
