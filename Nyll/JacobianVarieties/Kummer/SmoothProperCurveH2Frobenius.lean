/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIntegralSmooth
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
public import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Frobenius.ArithmeticComparison
public import Nyll.EtaleCohomology.Frobenius.RationalAdic
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Frobenius
public import Nyll.JacobianVarieties.Kummer.SmoothProperCurveH2
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# Actual geometric Frobenius and every H² trace of a curve

The actual model on the literal geometric base change supplies the
native degree theorem. The original constant-field isomorphism supplies
inverse arithmetic semilinearity, and the proved comparison with the
original geometric Frobenius gives its action on the original finite,
integral, and rational cohomology. No curve-model comparison or
cohomological equivariance is an additional hypothesis.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open EtaleCohomology.Classical

namespace EtaleCohomology

variable (k K : Type u) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [IsProper (X ↘ Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k))]

local notation "XK" => pullback (X ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))
local notation "cK" => pullback.snd (X ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))

omit [Fintype k] [IsAlgClosed K] [Algebra.IsAlgebraic k K]
  [IsProper (X ↘ Spec (CommRingCat.of k))] in
private theorem finiteFieldH2BaseChange_isIntegral : IsIntegral XK := by
  have : Smooth (X ↘ Spec (CommRingCat.of k)) :=
    SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (CommRingCat.of k))
  have : GeometricallyIntegral (X ↘ Spec (CommRingCat.of k)) :=
    geometricallyIntegral_of_smooth_of_geometricallyConnected (X ↘ Spec (CommRingCat.of k))
  infer_instance

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

include hℓ

/-- Actual geometric Frobenius multiplies the original finite H² by
the cardinality of the finite base field. -/
theorem finiteLevelH2_geometricFrobenius (n : ℕ)
    (a : finiteLevelCohomology XK ℓ n 2) :
    finiteLevelCohomologyPullback ℓ (Scheme.constantBaseChangeFrobenius k K X) n 2 a =
      (Fintype.card k) • a := by
  have : IsIntegral XK := finiteFieldH2BaseChange_isIntegral k K X
  let : Algebra K (Scheme.functionField XK) :=
    (AlgebraicCurve.baseToFunctionField cK).toAlgebra
  let M := AlgebraicCurve.CurveModel.ofSmoothProperCurve cK
  have hg := geometricFrobenius_eq_inverseArithmetic_on_constantCohomology
    k K X (ellPowerCoefficients ℓ n) 2 a
  change finiteLevelCohomologyPullback ℓ (Scheme.constantBaseChangeFrobenius k K X) n 2 a =
    finiteLevelCohomologyPullback ℓ (Scheme.constantFieldTwist k K X
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm) n 2 a at hg
  exact hg.trans (M.nativeFiniteLevelH2_inverseArithmetic k K ℓ hℓ
    (Scheme.constantFieldTwistIso k K X (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm)
    (Scheme.constantFieldTwist_snd k K X (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm)
    n a)

/-- The actual geometric Frobenius on the original integral inverse
limit is cardinality multiplication. -/
theorem ellAdicH2_geometricFrobenius_apply (a : ellAdicCohomology XK ℓ 2) :
    finiteFieldFrobeniusEllAdicCohomology k K X ℓ 2 a = (Fintype.card k) • a := by
  have : IsIntegral XK := finiteFieldH2BaseChange_isIntegral k K X
  let : Algebra K (Scheme.functionField XK) :=
    (AlgebraicCurve.baseToFunctionField cK).toAlgebra
  let M := AlgebraicCurve.CurveModel.ofSmoothProperCurve cK
  rw [finiteFieldFrobeniusEllAdicCohomology_eq_inverseArithmetic]
  exact M.nativeEllAdicH2_inverseArithmetic_apply k K ℓ hℓ
    (Scheme.constantFieldTwistIso k K X (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm)
    (Scheme.constantFieldTwist_snd k K X (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm) a

/-- The actual geometric Frobenius on the original rational scalar
extension is cardinality multiplication. -/
theorem rationalEllAdicH2_geometricFrobenius_apply
    (a : rationalEllAdicCohomology ℓ XK 2) :
    finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 2 a = (Fintype.card k) • a := by
  have : IsIntegral XK := finiteFieldH2BaseChange_isIntegral k K X
  let : Algebra K (Scheme.functionField XK) :=
    (AlgebraicCurve.baseToFunctionField cK).toAlgebra
  let M := AlgebraicCurve.CurveModel.ofSmoothProperCurve cK
  rw [finiteFieldFrobeniusRationalEllAdicCohomology_eq_inverseArithmetic]
  exact M.nativeRationalEllAdicH2_inverseArithmetic_apply k K ℓ hℓ
    (Scheme.constantFieldTwistIso k K X (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm)
    (Scheme.constantFieldTwist_snd k K X (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm) a

/-- Every power of the original geometric Frobenius acts by the
corresponding cardinality power on the original rational H². -/
theorem rationalEllAdicH2_geometricFrobenius_pow (m : ℕ) :
    (finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 2) ^ m =
      (Fintype.card k ^ m) •
        (1 : Module.End ℚ_[ℓ] (rationalEllAdicCohomology ℓ XK 2)) := by
  have : IsIntegral XK := finiteFieldH2BaseChange_isIntegral k K X
  let : Algebra K (Scheme.functionField XK) :=
    (AlgebraicCurve.baseToFunctionField cK).toAlgebra
  let M := AlgebraicCurve.CurveModel.ofSmoothProperCurve cK
  rw [finiteFieldFrobeniusRationalEllAdicCohomology_pow_eq_inverseArithmetic]
  exact M.nativeRationalEllAdicH2_inverseArithmetic_pow k K ℓ hℓ
    (Scheme.constantFieldTwistIso k K X (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm)
    (Scheme.constantFieldTwist_snd k K X (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm) m

/-- Every power of actual geometric Frobenius has trace q^m on the
original rational H² of a geometrically connected smooth proper curve. -/
theorem trace_rationalEllAdicH2_frobenius_pow (m : ℕ) :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ XK 2)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 2) ^ m) =
      (Fintype.card k : ℚ_[ℓ]) ^ m := by
  have : IsIntegral XK := finiteFieldH2BaseChange_isIntegral k K X
  let : Algebra K (Scheme.functionField XK) :=
    (AlgebraicCurve.baseToFunctionField cK).toAlgebra
  let M := AlgebraicCurve.CurveModel.ofSmoothProperCurve cK
  rw [finiteFieldFrobeniusRationalEllAdicCohomology_pow_eq_inverseArithmetic]
  exact M.trace_nativeRationalEllAdicH2_inverseArithmetic_pow k K ℓ hℓ
    (Scheme.constantFieldTwistIso k K X (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm)
    (Scheme.constantFieldTwist_snd k K X (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm) m

end EtaleCohomology
