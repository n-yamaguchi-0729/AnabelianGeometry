/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.Modulus.Modulus
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Divisors.CartierModulus
public import Nyll.AlgebraicCurves.Models.Divisors.CurveCartierDivisorCoordinates
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.EffectiveCartierIdeal
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.CartierAdicCycleClass
public import Nyll.EtaleCohomology.Classical.CartierCycleClass
public import Nyll.EtaleCohomology.Classical.CartierGenericUnitSections
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.JacobianVarieties.Kummer.CurveNativeAdicH2
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Boundary
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Degree
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Degree of the original Cartier cycle class on a curve

The actual local-equation section of an invertible ideal has its original
Cartier multiplicity divisor. Passing through the original generic-unit
and Kummer boundaries identifies the original Cartier cycle class with
the native class of that same divisor. Its finite, integral, and rational
degrees are therefore the full Cartier degree, including nonreduced
multiplicities.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory
open EtaleCohomology EtaleCohomology.Classical
open scoped TensorProduct

namespace AlgebraicCurve.CurveModel

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The actual finite Cartier class is the native finite class of its
original multiplicity divisor, with the same coherent coefficients. -/
theorem finiteEffectiveCartierCycleClass_eq_nativeDivisorClass
    (n : ℕ) (I : M.C.IdealSheafData) (hI : I.IsInvertible) :
    finiteEffectiveCartierCycleClass M.toBase ℓ hℓ n
        ⟨I, hI.isEffectiveCartier⟩ =
      M.nativeFiniteDivisorClass ℓ hℓ n (M.cartierModulus I hI).toDivisor := by
  let D : Scheme.EffectiveCartierDivisor M.C := ⟨I, hI.isEffectiveCartier⟩
  let e := finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 2
  have h := M.nativeFiniteDivisorClass_genericUnitBoundary ℓ hℓ n
    (effectiveCartierGenericUnitH0 D)
  rw [M.genericUnitDivisorH0Equiv_cartier I hI] at h
  calc
    finiteEffectiveCartierCycleClass M.toBase ℓ hℓ n D =
        e.symm (e (finiteEffectiveCartierCycleClass M.toBase ℓ hℓ n D)) :=
      (e.symm_apply_apply _).symm
    _ = e.symm (effectiveCartierCycleClass D
        (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
        (etaleKummerExponentUnit_of_base M.toBase
          (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))) :=
      congrArg e.symm (finiteEffectiveCartierCycleClass_kummer M.toBase ℓ hℓ n D)
    _ = M.nativeFiniteDivisorClass ℓ hℓ n (M.cartierModulus I hI).toDivisor := h.symm

/-- The degree of the original finite Cartier class is the original
Cartier degree modulo the original coefficient exponent. -/
theorem nativeFiniteLevelH2DegreeEquiv_cartier
    (n : ℕ) (I : M.C.IdealSheafData) (hI : I.IsInvertible) :
    M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
        (finiteEffectiveCartierCycleClass M.toBase ℓ hℓ n
          ⟨I, hI.isEffectiveCartier⟩) =
      ((M.cartierModulus I hI).degree : ZMod (ℓ ^ (n + 1))) := by
  rw [M.finiteEffectiveCartierCycleClass_eq_nativeDivisorClass ℓ hℓ n I hI,
    M.nativeFiniteLevelH2DegreeEquiv_divisor]
  rfl

/-- The original integral Cartier family is the compatible native
family of its actual multiplicity divisor. -/
theorem integralEffectiveCartierCycleClass_eq_nativeDivisorClass
    (I : M.C.IdealSheafData) (hI : I.IsInvertible) :
    integralEffectiveCartierCycleClass M.toBase ℓ hℓ
        ⟨I, hI.isEffectiveCartier⟩ =
      M.nativeEllAdicDivisorClass ℓ hℓ (M.cartierModulus I hI).toDivisor := by
  apply ellAdicCohomology_ext M.C ℓ 2
  intro n
  have hcartier := integralEffectiveCartierCycleClass_projection M.toBase ℓ hℓ
    (⟨I, hI.isEffectiveCartier⟩ : Scheme.EffectiveCartierDivisor M.C) n
  have hfinite := M.finiteEffectiveCartierCycleClass_eq_nativeDivisorClass ℓ hℓ n I hI
  have hnative := M.nativeEllAdicDivisorClass_projection ℓ hℓ
    (M.cartierModulus I hI).toDivisor n
  exact hcartier.trans (hfinite.trans hnative.symm)

/-- The original integral Cartier class retains the full Cartier
degree in the adic integers. -/
theorem nativeEllAdicH2DegreeEquiv_cartier
    (I : M.C.IdealSheafData) (hI : I.IsInvertible) :
    M.nativeEllAdicH2DegreeEquiv ℓ hℓ
        (integralEffectiveCartierCycleClass M.toBase ℓ hℓ
          ⟨I, hI.isEffectiveCartier⟩) =
      ((M.cartierModulus I hI).degree : ℤ_[ℓ]) := by
  rw [M.integralEffectiveCartierCycleClass_eq_nativeDivisorClass ℓ hℓ I hI,
    M.nativeEllAdicH2DegreeEquiv_divisor]
  rfl

/-- The actual rational Cartier class is scalar extension of the
native class of its original multiplicity divisor. -/
theorem rationalEffectiveCartierCycleClass_eq_nativeDivisorClass
    (I : M.C.IdealSheafData) (hI : I.IsInvertible) :
    rationalEffectiveCartierCycleClass M.toBase ℓ hℓ
        ⟨I, hI.isEffectiveCartier⟩ =
      (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]]
        M.nativeEllAdicDivisorClass ℓ hℓ (M.cartierModulus I hI).toDivisor := by
  change (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]]
      integralEffectiveCartierCycleClass M.toBase ℓ hℓ
        ⟨I, hI.isEffectiveCartier⟩ = _
  exact congrArg (fun a : ellAdicCohomology M.C ℓ 2 => (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] a)
    (M.integralEffectiveCartierCycleClass_eq_nativeDivisorClass ℓ hℓ I hI)

/-- The original rational Cartier cycle class has the full original
Cartier degree under the actual rational trace in degree two. -/
theorem nativeRationalEllAdicH2DegreeEquiv_cartier
    (I : M.C.IdealSheafData) (hI : I.IsInvertible) :
    M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        (rationalEffectiveCartierCycleClass M.toBase ℓ hℓ
          ⟨I, hI.isEffectiveCartier⟩) =
      ((M.cartierModulus I hI).degree : ℚ_[ℓ]) := by
  rw [M.rationalEffectiveCartierCycleClass_eq_nativeDivisorClass ℓ hℓ I hI,
    M.nativeRationalEllAdicH2DegreeEquiv_divisor]
  rfl

end AlgebraicCurve.CurveModel
