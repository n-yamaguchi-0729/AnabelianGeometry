/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
public import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.JacobianVarieties.Kummer.CurveNativeAdicH2
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Degree
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Original H² of a smooth proper integral curve

The existing concrete curve model on the original scheme supplies the
native degree comparisons without an auxiliary model or an isomorphism
hypothesis. Its function-field algebra is the one belonging to the
original structure map. The finite, integral, and rational comparisons
therefore have the original scheme as their source, and retain its
original coefficient reductions and inverse-limit projections.

The final base-change comparisons apply this construction to the literal
scheme pullback. Smoothness, properness, and integrality there are supplied
by the existing geometric base-change theorems.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits
open EtaleCohomology.Classical
open scoped TensorProduct

namespace AlgebraicGeometry.SmoothProperCurve

section OriginalCurve

variable (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
  (c : X ⟶ Spec (CommRingCat.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The native finite H² degree comparison on the original curve.
The model is constructed on that same scheme and its actual function field. -/
def nativeFiniteLevelH2DegreeEquiv (n : ℕ) :
    finiteLevelCohomology X ℓ n 2 ≃+ ZMod (ℓ ^ (n + 1)) := by
  let : Algebra K X.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  exact (AlgebraicCurve.CurveModel.ofSmoothProperCurve c).nativeFiniteLevelH2DegreeEquiv ℓ hℓ n

/-- Original finite coefficient reductions become the original
residue-ring reductions under degree. -/
theorem nativeFiniteLevelH2DegreeEquiv_reduction (n : ℕ)
    (a : finiteLevelCohomology X ℓ (n + 1) 2) :
    nativeFiniteLevelH2DegreeEquiv K c ℓ hℓ n (finiteLevelReduction X ℓ n 2 a) =
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) (ZMod (ℓ ^ (n + 1)))
        (nativeFiniteLevelH2DegreeEquiv K c ℓ hℓ (n + 1) a) := by
  let : Algebra K X.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  exact (AlgebraicCurve.CurveModel.ofSmoothProperCurve c).nativeFiniteLevelH2DegreeEquiv_reduction
    ℓ hℓ n a

/-- The original integral inverse limit is one copy of the adic integers. -/
def nativeEllAdicH2DegreeEquiv : ellAdicCohomology X ℓ 2 ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] := by
  let : Algebra K X.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  exact (AlgebraicCurve.CurveModel.ofSmoothProperCurve c).nativeEllAdicH2DegreeEquiv ℓ hℓ

/-- Degree retains every original finite projection. -/
theorem nativeEllAdicH2DegreeEquiv_reduction (a : ellAdicCohomology X ℓ 2) (n : ℕ) :
    PadicInt.toZModPow (n + 1) (nativeEllAdicH2DegreeEquiv K c ℓ hℓ a) =
      nativeFiniteLevelH2DegreeEquiv K c ℓ hℓ n (ellAdicProjection X ℓ 2 n a) := by
  let : Algebra K X.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  exact (AlgebraicCurve.CurveModel.ofSmoothProperCurve c).nativeEllAdicH2DegreeEquiv_reduction
    ℓ hℓ a n

/-- The inverse degree comparison retains the original finite inverse
degree maps at every coefficient level. -/
theorem nativeEllAdicH2DegreeEquiv_symm_projection (r : ℤ_[ℓ]) (n : ℕ) :
    ellAdicProjection X ℓ 2 n ((nativeEllAdicH2DegreeEquiv K c ℓ hℓ).symm r) =
      (nativeFiniteLevelH2DegreeEquiv K c ℓ hℓ n).symm (PadicInt.toZModPow (n + 1) r) := by
  let : Algebra K X.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  exact (AlgebraicCurve.CurveModel.ofSmoothProperCurve c).nativeEllAdicH2DegreeEquiv_symm_projection
    ℓ hℓ r n

/-- The original rational H² is one copy of the adic field. -/
def nativeRationalEllAdicH2DegreeEquiv :
    rationalEllAdicCohomology ℓ X 2 ≃ₗ[ℚ_[ℓ]] ℚ_[ℓ] := by
  let : Algebra K X.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  exact (AlgebraicCurve.CurveModel.ofSmoothProperCurve c).nativeRationalEllAdicH2DegreeEquiv ℓ hℓ

/-- Rational degree is scalar extension of the original integral degree. -/
theorem nativeRationalEllAdicH2DegreeEquiv_tmul
    (q : ℚ_[ℓ]) (a : ellAdicCohomology X ℓ 2) :
    nativeRationalEllAdicH2DegreeEquiv K c ℓ hℓ (q ⊗ₜ[ℤ_[ℓ]] a) =
      nativeEllAdicH2DegreeEquiv K c ℓ hℓ a • q := by
  let : Algebra K X.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  exact (AlgebraicCurve.CurveModel.ofSmoothProperCurve c).nativeRationalEllAdicH2DegreeEquiv_tmul
    ℓ hℓ q a

include c hℓ in
/-- The original finite H² has the cardinality of one coefficient group. -/
theorem nativeFiniteLevelH2_card (n : ℕ) :
    Nat.card (finiteLevelCohomology X ℓ n 2) = ℓ ^ (n + 1) := by
  let : Algebra K X.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  exact (AlgebraicCurve.CurveModel.ofSmoothProperCurve c).nativeFiniteLevelH2_card ℓ hℓ n

include c hℓ in
/-- The original integral H² is finite and free. -/
theorem nativeEllAdicH2_finite_free :
    Module.Free ℤ_[ℓ] (ellAdicCohomology X ℓ 2) ∧
      Module.Finite ℤ_[ℓ] (ellAdicCohomology X ℓ 2) := by
  let : Algebra K X.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  exact (AlgebraicCurve.CurveModel.ofSmoothProperCurve c).nativeEllAdicH2_finite_free ℓ hℓ

include c hℓ in
/-- The original integral H² has rank one. -/
theorem nativeEllAdicH2_finrank : Module.finrank ℤ_[ℓ] (ellAdicCohomology X ℓ 2) = 1 := by
  let : Algebra K X.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  exact (AlgebraicCurve.CurveModel.ofSmoothProperCurve c).nativeEllAdicH2_finrank ℓ hℓ

include c hℓ in
/-- The original rational H² is finite-dimensional. -/
theorem nativeRationalEllAdicH2_finiteDimensional :
    FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ X 2) := by
  let : Algebra K X.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  exact (AlgebraicCurve.CurveModel.ofSmoothProperCurve c).nativeRationalEllAdicH2_finiteDimensional
    ℓ hℓ

include c hℓ in
/-- The original rational H² has dimension one. -/
theorem nativeRationalEllAdicH2_finrank :
    Module.finrank ℚ_[ℓ] (rationalEllAdicCohomology ℓ X 2) = 1 := by
  let : Algebra K X.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  exact (AlgebraicCurve.CurveModel.ofSmoothProperCurve c).nativeRationalEllAdicH2_finrank ℓ hℓ

end OriginalCurve

section LiteralBaseChange

variable (R : Type u) [CommRing R] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
  [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (K : Type u) [Field K] [IsAlgClosed K]
  (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- Finite H² degree on the literal original base-change scheme. -/
def nativeFiniteLevelH2DegreeEquivBaseChange (n : ℕ) :
    finiteLevelCohomology (pullback c s) ℓ n 2 ≃+ ZMod (ℓ ^ (n + 1)) :=
  nativeFiniteLevelH2DegreeEquiv K (pullback.snd c s) ℓ hℓ n

/-- Integral H² degree on the literal original base-change scheme. -/
def nativeEllAdicH2DegreeEquivBaseChange :
    ellAdicCohomology (pullback c s) ℓ 2 ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] :=
  nativeEllAdicH2DegreeEquiv K (pullback.snd c s) ℓ hℓ

/-- Rational H² degree on the literal original base-change scheme. -/
def nativeRationalEllAdicH2DegreeEquivBaseChange :
    rationalEllAdicCohomology ℓ (pullback c s) 2 ≃ₗ[ℚ_[ℓ]] ℚ_[ℓ] :=
  nativeRationalEllAdicH2DegreeEquiv K (pullback.snd c s) ℓ hℓ

include hℓ in
/-- Rational H² of the literal geometric base change is finite-dimensional. -/
theorem nativeRationalEllAdicH2_finiteDimensional_baseChange :
    FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ (pullback c s) 2) :=
  nativeRationalEllAdicH2_finiteDimensional K (pullback.snd c s) ℓ hℓ

include hℓ in
/-- Rational H² of the literal geometric base change has dimension one. -/
theorem nativeRationalEllAdicH2_finrank_baseChange :
    Module.finrank ℚ_[ℓ] (rationalEllAdicCohomology ℓ (pullback c s) 2) = 1 :=
  nativeRationalEllAdicH2_finrank K (pullback.snd c s) ℓ hℓ

end LiteralBaseChange

end AlgebraicGeometry.SmoothProperCurve
