/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
public import Nyll.AlgebraicCurves.Models.Kummer.CurveNativeH1Picard
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProductIntegral
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.EtaleCohomology.Classical.AbelianCechComponentDetection
public import Nyll.EtaleCohomology.Classical.AbelianCechPullback
public import Nyll.EtaleCohomology.Classical.AbelianCechResidualDescent
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicCupH1Anticommutativity
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.CartierAdicCycleClass
public import Nyll.EtaleCohomology.Classical.CartierCycleClass
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.CupCechKernelProduct
public import Nyll.EtaleCohomology.Classical.CurveOverlapComponents
public import Nyll.EtaleCohomology.Classical.DiagonalDivisorBundle
public import Nyll.EtaleCohomology.Classical.DiagonalPoincareFamily
public import Nyll.EtaleCohomology.Classical.ExternalCupPullbackComposition
public import Nyll.EtaleCohomology.Classical.FiniteCechKernelCup
public import Nyll.EtaleCohomology.Classical.FiniteCechKernelCupRestriction
public import Nyll.EtaleCohomology.Classical.FiniteDiagonalSections
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.FiniteLevelScalarApproximation
public import Nyll.EtaleCohomology.Classical.GraphCartierCycleClass
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.RationalKunnethSections
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.GaloisSections
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
public import Nyll.JacobianVarieties.Kummer.CurveDiagonalFirstRelation
public import Nyll.JacobianVarieties.Kummer.CurveDiagonalFiniteKernel
public import Nyll.JacobianVarieties.Kummer.CurveDiagonalFiniteDescent
public import Nyll.JacobianVarieties.Kummer.CurveDiagonalFiniteTransgression
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionBaseChangeDescent
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionCupOverlap
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionCupSum
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionIntegralRoot
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionRoot
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionRootNativeOverlap
public import Nyll.JacobianVarieties.Kummer.CurveNativeCupPairing
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleConnected
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Module.LinearMap.End

/-!
# The actual normalized diagonal at every finite coefficient level

The retained Picard division root and the original finite cup kernels
have the same overlap classes after multiplication by the denominator
of the integral tensor. Their difference descends from the parameter
curve. The original point section kills that difference. Every class,
coefficient map and covering kernel in this calculation is the original
one used by the finite and adic cohomology constructions.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Abelian
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicCurve.CurveModel

/-- The original finite normalized diagonal is the external cup sum
of an integral tensor with the same original cup contraction. The
division cover, its root and all its overlap classes are constructed
inside the proof. -/
theorem finiteDiagonalSignedCycleClass_eq_integralCupSum
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    [GeometricallyIntegral c]
    (p : Spec (.of K) ⟶ C) (hp : p ≫ c = 𝟙 _)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    let M := literalCurveModel c
    let _ : IsIntegral (pullback c c) := isIntegral_pullback_of_smooth_of_isAlgClosed c c
    ∀ (r : ℤ_[ℓ]) (S : Finset (ellAdicCohomology C ℓ 1 × ellAdicCohomology C ℓ 1)),
      (∀ z : ellAdicCohomology C ℓ 1, ∑ v ∈ S,
        M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl z v.2 • v.1 = (-r) • z) →
      ∀ n : ℕ,
        r • (finiteEffectiveCartierCycleClass (pullback.snd c c ≫ c) ℓ hℓ n
            (graphEffectiveCartierDivisor c c (𝟙 C) (Category.id_comp c)) -
          finiteEffectiveCartierCycleClass (pullback.snd c c ≫ c) ℓ hℓ n
            (diagonalEdgeEffectiveCartierDivisor c p hp)) =
          ∑ v ∈ S, finiteLevelCup (pullback c c) ℓ n 1 1 2 rfl
            (finiteLevelCohomologyPullback ℓ (pullback.fst c c) n 1
              (ellAdicProjection C ℓ 1 n v.1))
            (finiteLevelCohomologyPullback ℓ (pullback.snd c c) n 1
              (ellAdicProjection C ℓ 1 n v.2)) := by
  dsimp only
  intro r S hS n
  let N := ℓ ^ (n + 1)
  have hnK : IsUnit (N : K) := by
    simpa only [N, Nat.cast_pow] using hℓ.pow (n + 1)
  obtain ⟨D, hD, hs, hproper, hconnected, B₀, i, hB₀, -, hqfinite, hqetale, hqsurj, ⟨eRoot⟩⟩ :=
    diagonalMiddleBundle_exists_integral_picard_division_root c p hp N hnK
  have : Smooth D.toBase := hs
  have : IsProper D.toBase := hproper
  have : GeometricallyConnected D.toBase := hconnected
  let aj := diagonalPicardClassifyingMap c p hp D hD
  let q₀ := i ≫ hD.divisionProjection aj N
  have : IsFinite q₀ := hqfinite
  have : Etale q₀ := hqetale
  have : IsFiniteEtale q₀ := IsFiniteEtale.mk
  let B : FiniteEtale C := FiniteEtale.mk q₀
  have : IsIntegral B.left := hB₀
  have : Surjective B.hom := hqsurj
  have h := finiteDiagonalSignedCycleClass_eq_integralCupSum_of_division_root
    c p hp ℓ hℓ D hD B n i rfl eRoot r S hS
  exact h

end AlgebraicCurve.CurveModel
