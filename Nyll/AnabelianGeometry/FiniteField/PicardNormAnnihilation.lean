/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.PicardNormFixed
public import Nyll.AlgebraicCurves.Models.ConstantExtension.PicardFrobenius
public import Nyll.AlgebraicCurves.Models.ConstantExtension.PicardDescent
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# One finite constant norm annihilates an actual fixed class

The positive-power fixed degree-zero subgroup of the original geometric
Picard group is finite. A constant extension of degree the period times
its cardinality therefore has zero norm on every degree-zero class fixed
by that power. The proof uses the original divisor norm and actual Picard
pullback; an infinite compatible family is unnecessary.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

namespace CyclicAction

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- A cyclic norm of length the period times an annihilator is zero. -/
theorem norm_sum_eq_zero_of_periodic_and_annihilated
    (σ : G) (x : A) (r N : ℕ) (hperiod : σ ^ r • x = x) (hN : N • x = 0) :
    (∑ i ∈ Finset.range (r * N), σ ^ i • x) = 0 := by
  have hmultiple (t : ℕ) : σ ^ (r * t) • x = x := by
    rw [pow_mul]
    induction t with
    | zero => rw [pow_zero, one_smul]
    | succ t ih => rw [pow_succ', mul_smul, ih, hperiod]
  have hblocks (t : ℕ) :
      (∑ i ∈ Finset.range (r * t), σ ^ i • x) =
        t • ∑ i ∈ Finset.range r, σ ^ i • x := by
    induction t with
    | zero => rw [Nat.mul_zero, Finset.range_zero, Finset.sum_empty, zero_nsmul]
    | succ t ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.add_comm (r * t) i, pow_add, mul_smul, hmultiple]
  have hnsmul (g : G) (t : ℕ) : t • (g • x) = g • (t • x) := by
    induction t with
    | zero => rw [zero_nsmul, zero_nsmul, smul_zero]
    | succ t ih => rw [succ_nsmul, succ_nsmul, smul_add, ih]
  rw [hblocks, Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [hnsmul, hN, smul_zero]

end CyclicAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicCurve.CurveModel

variable {k κ K : Type uGeom} {F : Type uField₁} [Field k] [Fintype k] [Field κ] [IsAlgClosed κ]
    [Algebra k κ] [Algebra.IsAlgebraic k κ]
    [Field K] [Algebra k K] [IsCurveOver k K] [Algebra.EssFiniteType k K]
    [Field F] [Algebra κ F] [IsCurveOver κ F]
    (M₀ : CurveModel k K) [GeometricallyIntegral M₀.toBase]
    (M : CurveModel κ F) (e : M.C ≅ pullback M₀.toBase (specMap k κ))
    (he : e.hom ≫ pullback.snd M₀.toBase (specMap k κ) = M.toBase)

local notation "φ" => M.constantSemilinearAction M₀.toBase e he
  (FiniteField.frobeniusAlgEquivOfAlgebraic k κ)

/-- The actual finite-constant divisor norm vanishes on every original
degree-zero class fixed by the specified Frobenius power, once its degree
is the period times the cardinality of the actual finite fixed subgroup. -/
theorem constantPicardNorm_eq_zero_of_fixed_of_finrank
    (r : ℕ) (hr : r ≠ 0)
    (E : Type uGeom) [Field E] [Fintype E] [Algebra k E] [Algebra E κ]
    [IsScalarTower k E κ] [Algebra.IsAlgebraic E κ]
    (hd : Module.finrank k E =
      r * Nat.card (M₀.constantPicardZeroFixedSubgroup M e he r)) :
    let CE := pullback M₀.toBase (specMap k E)
    let cE := pullback.snd M₀.toBase (specMap k E)
    let _ : Algebra E CE.functionField := (baseToFunctionField cE).toAlgebra
    let _ : IsCurveOver E CE.functionField :=
      isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one cE
        (RingEquiv.refl _) (fun _ => rfl)
    ∀ x : Pic E CE.functionField,
      H1Gm.degree E CE.functionField x = 0 →
      (M₀.constantFiniteSemilinearFrobenius M e he E) ^ r • x = x →
      M₀.constantPicardNorm M e he E x = 0 := by
  intro CE cE aE hcurve x hdegree hfixed
  have hfinite : Finite (M₀.constantPicardZeroFixedSubgroup M e he r) :=
    M₀.finite_constantPicardZeroFixedSubgroup M e he r hr
  let P := M₀.constantPicardPeriodicEquiv M e he E
  let ψ := M₀.constantFiniteSemilinearFrobenius M e he E
  have hpow (t : ℕ) (z : Pic E CE.functionField) :
      (P (ψ ^ t • z) : Pic κ F) = φ ^ t • (P z : Pic κ F) := by
    induction t with
    | zero => rw [pow_zero, one_smul, pow_zero, one_smul]
    | succ t ih =>
      rw [pow_succ', mul_smul, pow_succ', mul_smul]
      exact (M₀.constantPicardPeriodicEquiv_finiteFrobenius M e he E _).trans
        (congrArg (fun a : Pic κ F => φ • a) ih)
  have hyperiod : φ ^ r • (P x : Pic κ F) = (P x : Pic κ F) := by
    rw [← hpow, hfixed]
  have hydegree : H1Gm.degree κ F (P x : Pic κ F) = 0 :=
    (M₀.degree_constantPicardPeriodicEquiv M e he E x).trans hdegree
  have hyann : Nat.card (M₀.constantPicardZeroFixedSubgroup M e he r) •
      (P x : Pic κ F) = 0 :=
    congrArg Subtype.val (card_nsmul_eq_zero'
      (x := (⟨(P x : Pic κ F), hydegree, hyperiod⟩ :
        M₀.constantPicardZeroFixedSubgroup M e he r)))
  have hC : ConstantsAreBase k K := M₀.constantsAreBase_of_constantModel M e he
  apply M₀.constantPicardBaseChange_injective M e he hC
  rw [map_zero, M₀.constantPicardBaseChange_norm M e he E]
  have hsum := CyclicAction.norm_sum_eq_zero_of_periodic_and_annihilated
    φ (P x : Pic κ F) r
    (Nat.card (M₀.constantPicardZeroFixedSubgroup M e he r)) hyperiod hyann
  exact (congrArg
    (fun d : ℕ => ∑ i ∈ Finset.range d, φ ^ i • (P x : Pic κ F)) hd).trans hsum

end AlgebraicCurve.CurveModel
