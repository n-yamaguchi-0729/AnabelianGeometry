/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitDivisorCoordinates
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitIsoDegree
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.GenericUnitOpenCohomology
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.JacobianVarieties.Kummer.CurveNativeAdicH2
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2ArithmeticBoundary
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Boundary
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Degree
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# The original H² action of inverse arithmetic Frobenius

The proved isomorphism invariance of actual divisor degree combines with
the original arithmetic boundary calculation. Surjectivity of the actual
divisor-class map then gives cardinality multiplication on the original
finite H². The original inverse limit and scalar extension retain this
action, and every power has the expected trace on the rank-one module.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory
open EtaleCohomology EtaleCohomology.Classical
open scoped TensorProduct

namespace AlgebraicCurve.CurveModel

variable (k K : Type u) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  {F : Type u} [Field F] [Algebra K F]
  (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))
  (e : M.C ≅ M.C)
  (he : e.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom
    (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm.toRingHom))

include hℓ he

/-- Actual inverse arithmetic Frobenius acts by the finite-field
cardinality on the original finite coefficient H². -/
theorem nativeFiniteLevelH2_inverseArithmetic (n : ℕ)
    (a : finiteLevelCohomology M.C ℓ n 2) :
    finiteLevelCohomologyPullback ℓ e.hom n 2 a = (Fintype.card k) • a := by
  obtain ⟨D, rfl⟩ := M.nativeFiniteDivisorClass_surjective ℓ hℓ n a
  let b := M.genericUnitDivisorH0Equiv.symm D
  have hb : M.genericUnitDivisorH0Equiv b = D :=
    M.genericUnitDivisorH0Equiv.apply_symm_apply D
  have ha :
      finiteLevelCohomologyPullback ℓ e.hom n 2 (M.nativeFiniteDivisorClass ℓ hℓ n D) =
        (Fintype.card k) • M.nativeFiniteDivisorClass ℓ hℓ n
          (M.genericUnitDivisorH0Equiv
            (etaleGenericUnitQuotientCohomologyPullback e.hom 0 b)) := by
    simpa only [hb] using
      M.nativeFiniteDivisorClass_inverseArithmetic k K ℓ hℓ e he n b
  apply (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n).injective
  simp only [ha, map_nsmul, nativeFiniteLevelH2DegreeEquiv_divisor,
    M.genericUnitDivisorH0Equiv_degree_iso_pullback M e b, hb]

/-- The actual action on the original integral inverse limit is
the same cardinality multiplication at every original projection. -/
theorem nativeEllAdicH2_inverseArithmetic_apply
    (a : ellAdicCohomology M.C ℓ 2) :
    ellAdicCohomologyPullback ℓ e.hom 2 a = (Fintype.card k) • a := by
  apply ellAdicCohomology_ext M.C ℓ 2
  intro n
  change finiteLevelCohomologyPullback ℓ e.hom n 2 (a.val n) =
    (Fintype.card k) • a.val n
  exact M.nativeFiniteLevelH2_inverseArithmetic k K ℓ hℓ e he n (a.val n)

/-- The original rational scalar extension retains the cardinality
action, without replacing its original tensor-product cohomology. -/
theorem nativeRationalEllAdicH2_inverseArithmetic_apply
    (a : rationalEllAdicCohomology ℓ M.C 2) :
    rationalEllAdicCohomologyPullback ℓ e.hom 2 a = (Fintype.card k) • a := by
  induction a using TensorProduct.inductionOn with
  | tmul q a =>
      have hpull := rationalEllAdicCohomologyPullback_tmul ℓ e.hom 2 q a
      have hnative := M.nativeEllAdicH2_inverseArithmetic_apply k K ℓ hℓ e he a
      have htmul := congrArg
        (fun b : ellAdicCohomology M.C ℓ 2 => q ⊗ₜ[ℤ_[ℓ]] b) hnative
      have hsmul := map_nsmul
        (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (ellAdicCohomology M.C ℓ 2) q) (Fintype.card k) a
      exact hpull.trans (htmul.trans hsmul)
  | add a b ha hb =>
      have hmap := (rationalEllAdicCohomologyPullback ℓ e.hom 2).map_add a b
      have hsum := congrArg₂
        (fun x y : rationalEllAdicCohomology ℓ M.C 2 => x + y) ha hb
      exact hmap.trans (hsum.trans (smul_add (Fintype.card k) a b).symm)

/-- Every power acts by the corresponding power of the original
finite-field cardinality on the original rational H². -/
theorem nativeRationalEllAdicH2_inverseArithmetic_pow (m : ℕ) :
    (rationalEllAdicCohomologyPullback ℓ e.hom 2) ^ m =
      (Fintype.card k ^ m) •
        (1 : Module.End ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 2)) := by
  induction m with
  | zero =>
      rw [pow_zero, pow_zero, one_nsmul]
  | succ m ih =>
      apply LinearMap.ext
      intro a
      change ((rationalEllAdicCohomologyPullback ℓ e.hom 2) ^ (m + 1)) a =
        (Fintype.card k ^ (m + 1)) • a
      rw [pow_succ']
      change rationalEllAdicCohomologyPullback ℓ e.hom 2
        (((rationalEllAdicCohomologyPullback ℓ e.hom 2) ^ m) a) = _
      rw [ih]
      change rationalEllAdicCohomologyPullback ℓ e.hom 2
        ((Fintype.card k ^ m) • a) = (Fintype.card k ^ (m + 1)) • a
      rw [map_nsmul, nativeRationalEllAdicH2_inverseArithmetic_apply k K M ℓ hℓ e he,
        pow_succ, mul_nsmul]
      exact smul_comm (Fintype.card k ^ m) (Fintype.card k) a

/-- Every inverse-arithmetic Frobenius power has the expected trace
on the original rational degree-two cohomology. -/
theorem trace_nativeRationalEllAdicH2_inverseArithmetic_pow (m : ℕ) :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 2)
        ((rationalEllAdicCohomologyPullback ℓ e.hom 2) ^ m) =
      (Fintype.card k : ℚ_[ℓ]) ^ m := by
  have : FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 2) :=
    M.nativeRationalEllAdicH2_finiteDimensional ℓ hℓ
  rw [nativeRationalEllAdicH2_inverseArithmetic_pow k K M ℓ hℓ e he,
    map_nsmul, LinearMap.trace_one, M.nativeRationalEllAdicH2_finrank ℓ hℓ,
    Nat.cast_one, nsmul_eq_mul, mul_one, Nat.cast_pow]

end AlgebraicCurve.CurveModel
