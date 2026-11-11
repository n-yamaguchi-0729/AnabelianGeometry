/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralAlgClosed
public import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
public import Nyll.AlgebraicCurves.Models.Points.RationalPointExistence
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicCup
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.CartierAdicCycleClass
public import Nyll.EtaleCohomology.Classical.DiagonalDivisorBundle
public import Nyll.EtaleCohomology.Classical.DiagonalSignedCycleClass
public import Nyll.EtaleCohomology.Classical.GraphCartierCycleClass
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalKunnethMap
public import Nyll.JacobianVarieties.Kummer.CurveDiagonalEdgeClass
public import Nyll.JacobianVarieties.Kummer.CurveDiagonalFiniteTensor
public import Nyll.JacobianVarieties.Kummer.CurveTensorIntegralExpansion
public import Nyll.JacobianVarieties.Kummer.CurveTensorTrace
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The original diagonal and the negative identity tensor

One integral finite family represents a nonzero multiple of the rational
negative identity tensor. The original finite diagonal calculation identifies
that same family with the normalized diagonal at every coefficient level.
Passing through the actual inverse limit and scalar extension, then cancelling
the denominator, gives the equality in the original product cohomology.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open EtaleCohomology EtaleCohomology.Classical
open scoped TensorProduct

namespace AlgebraicCurve.CurveModel

/-- Projection detects a scalar multiple and a finite sum in the actual inverse limit. -/
private theorem ellAdic_smul_eq_sum_of_projection
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ)
    {ι : Type u} (r : ℤ_[ℓ]) (a : ellAdicCohomology X ℓ i)
    (S : Finset ι) (b : ι → ellAdicCohomology X ℓ i)
    (h : ∀ n, r • ellAdicProjection X ℓ i n a =
      ∑ v ∈ S, ellAdicProjection X ℓ i n (b v)) :
    r • a = ∑ v ∈ S, b v := by
  apply ellAdicCohomology_ext X ℓ i
  intro n
  exact (h n).trans (map_sum (ellAdicProjection X ℓ i n) b S).symm

/-- Scalar extension of an integral finite sum determines the original rational class. -/
private theorem eq_linearMap_of_integral_sum
    {R : Type*} [CommRing R] {Q : Type*} [Field Q] [Algebra R Q]
    {A : Type*} [AddCommGroup A] [Module R A]
    {B : Type*} [AddCommGroup B] [Module R B] [Module Q B] [IsScalarTower R Q B]
    {T : Type*} [AddCommGroup T] [Module Q T] {ι : Type*}
    (j : A →ₗ[R] B) (k : T →ₗ[Q] B) (r : R) (x : A) (y : B) (t : T)
    (S : Finset ι) (f : ι → A) (g : ι → T)
    (hIntegral : r • x = ∑ v ∈ S, f v) (hMiddle : j x = y)
    (hTerm : ∀ v, j (f v) = k (g v))
    (hTensor : (∑ v ∈ S, g v) = algebraMap R Q r • t)
    (hr : algebraMap R Q r ≠ 0) : y = k t := by
  apply smul_right_injective B hr
  calc
    algebraMap R Q r • y = j (r • x) := by
      rw [j.map_smul, hMiddle, algebraMap_smul]
    _ = ∑ v ∈ S, j (f v) := by rw [hIntegral, map_sum]
    _ = k (∑ v ∈ S, g v) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun v _ => hTerm v)
    _ = _ := by rw [hTensor, map_smul]

/-- Evaluation preserves the middle-class identity in the actual product cohomology. -/
theorem nativeRationalDiagonalMiddleClass_map_eq_negativeIdentityTensor
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    let M := literalCurveModel c
    ∀ {A : Type*} (eval : rationalEllAdicCohomology ℓ (pullback c c) 2 → A),
      eval (M.nativeRationalDiagonalMiddleClass ℓ hℓ) =
        eval (rationalEllAdicKunnethComponent ℓ c c 1 1 2 rfl
          (M.nativeRationalH1NegativeIdentityTensor ℓ hℓ)) := by
  classical
  intro algKF M A eval
  have : GeometricallyIntegral c := geometricallyIntegral_of_isAlgClosed c
  have : IsIntegral (pullback c c) := M.selfProduct_isIntegral
  obtain ⟨pM⟩ := M.nonempty_rationalPoint
  let p : NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of K))) c := pM
  have hExpansion :=
    (literalCurveModel c).exists_nativeH1_negativeIdentityTensor_integral_expansion ℓ hℓ
  obtain ⟨r, hr, SM, hTensor, hIntegral, _⟩ := hExpansion
  have hResult := by
    as_aux_lemma =>
      let S : Finset (ellAdicCohomology C ℓ 1 × ellAdicCohomology C ℓ 1) := SM
      let D := graphEffectiveCartierDivisor c c (𝟙 C) (Category.id_comp c)
      let E := diagonalEdgeEffectiveCartierDivisor c p.1 p.2
      let α : ellAdicCohomology (pullback c c) ℓ 2 :=
        integralEffectiveCartierCycleClass (pullback.snd c c ≫ c) ℓ hℓ D -
          integralEffectiveCartierCycleClass (pullback.snd c c ≫ c) ℓ hℓ E
      let β (v : ellAdicCohomology C ℓ 1 × ellAdicCohomology C ℓ 1) :
          ellAdicCohomology (pullback c c) ℓ 2 :=
        ellAdicCup (pullback c c) ℓ 1 1 2 rfl
          (ellAdicCohomologyPullback ℓ (pullback.fst c c) 1 v.1)
          (ellAdicCohomologyPullback ℓ (pullback.snd c c) 1 v.2)
      have hFinite := by
        as_aux_lemma =>
          exact finiteDiagonalSignedCycleClass_eq_integralCupSum c p.1 p.2 ℓ hℓ
            r S hIntegral
      have hAdic : r • α = ∑ v ∈ S, β v :=
        ellAdic_smul_eq_sum_of_projection (pullback c c) ℓ 2 r α S β hFinite
      let : Module ℤ_[ℓ] (rationalEllAdicCohomology ℓ (pullback c c) 2) :=
        inferInstanceAs (Module ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] ellAdicCohomology (pullback c c) ℓ 2))
      have : IsScalarTower ℤ_[ℓ] ℚ_[ℓ] (rationalEllAdicCohomology ℓ (pullback c c) 2) :=
        inferInstanceAs
          (IsScalarTower ℤ_[ℓ] ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] ellAdicCohomology (pullback c c) ℓ 2))
      let j : ellAdicCohomology (pullback c c) ℓ 2 →ₗ[ℤ_[ℓ]]
          rationalEllAdicCohomology ℓ (pullback c c) 2 :=
        TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (ellAdicCohomology (pullback c c) ℓ 2) 1
      let middle : rationalEllAdicCohomology ℓ (pullback c c) 2 :=
        M.nativeRationalDiagonalMiddleClass ℓ hℓ
      let identityTensor : rationalEllAdicCohomology ℓ C 1 ⊗[ℚ_[ℓ]]
          rationalEllAdicCohomology ℓ C 1 := M.nativeRationalH1NegativeIdentityTensor ℓ hℓ
      let j₁ : ellAdicCohomology C ℓ 1 → rationalEllAdicCohomology ℓ C 1 :=
        fun x => (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x
      have hTensorC : (∑ v ∈ S, j₁ v.1 ⊗ₜ[ℚ_[ℓ]] j₁ v.2) =
          algebraMap ℤ_[ℓ] ℚ_[ℓ] r • identityTensor := hTensor
      have hMiddle : j α = middle := by
        change j (integralEffectiveCartierCycleClass
            (pullback.snd c c ≫ c) ℓ hℓ D -
          integralEffectiveCartierCycleClass
            (pullback.snd c c ≫ c) ℓ hℓ E) = _
        rw [map_sub]
        change rationalEffectiveCartierCycleClass (pullback.snd c c ≫ c) ℓ hℓ D -
          rationalEffectiveCartierCycleClass (pullback.snd c c ≫ c) ℓ hℓ E = _
        rw [← rationalDiagonalMiddleClass_eq_signedCycleClass c p.1 p.2 ℓ hℓ]
        exact M.rationalDiagonalMiddleClass_eq_native ℓ hℓ p.1 p.2
      have hTerm (v : ellAdicCohomology C ℓ 1 × ellAdicCohomology C ℓ 1) :
          j (β v) = rationalEllAdicKunnethComponent ℓ c c 1 1 2 rfl
            (j₁ v.1 ⊗ₜ[ℚ_[ℓ]] j₁ v.2) := by
        have hk := rationalEllAdicKunnethComponent_tmul ℓ c c 1 1 2 rfl (j₁ v.1) (j₁ v.2)
        have he := rationalEllAdicExternalCup_tmul ℓ c c 1 1 2 rfl 1 1 v.1 v.2
        have hone := congrArg (fun q : ℚ_[ℓ] => q ⊗ₜ[ℤ_[ℓ]] β v) (one_mul (1 : ℚ_[ℓ]))
        exact (hk.trans (he.trans hone)).symm
      have hrQ : algebraMap ℤ_[ℓ] ℚ_[ℓ] r ≠ 0 := by
        intro h
        apply hr
        apply FaithfulSMul.algebraMap_injective ℤ_[ℓ] ℚ_[ℓ]
        exact h.trans (map_zero (algebraMap ℤ_[ℓ] ℚ_[ℓ])).symm
      have heq := eq_linearMap_of_integral_sum j (rationalEllAdicKunnethComponent ℓ c c 1 1 2 rfl)
        r α middle identityTensor S β (fun v => j₁ v.1 ⊗ₜ[ℚ_[ℓ]] j₁ v.2)
        hAdic hMiddle hTerm hTensorC hrQ
      exact congrArg eval heq
  exact hResult

/-- The middle class of the actual curve diagonal is the original Künneth
image of the negative identity tensor for its actual native cup pairing.
The auxiliary point and common integral denominator are constructed internally. -/
theorem nativeRationalDiagonalMiddleClass_eq_negativeIdentityTensor
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    let M := literalCurveModel c
    Eq (α := rationalEllAdicCohomology ℓ (pullback c c) 2)
      (M.nativeRationalDiagonalMiddleClass ℓ hℓ)
      (rationalEllAdicKunnethComponent ℓ c c 1 1 2 rfl
        (M.nativeRationalH1NegativeIdentityTensor ℓ hℓ)) := by
  intro algKF M
  exact nativeRationalDiagonalMiddleClass_map_eq_negativeIdentityTensor c ℓ hℓ
    (id : rationalEllAdicCohomology ℓ (pullback c c) 2 →
      rationalEllAdicCohomology ℓ (pullback c c) 2)

end AlgebraicCurve.CurveModel
