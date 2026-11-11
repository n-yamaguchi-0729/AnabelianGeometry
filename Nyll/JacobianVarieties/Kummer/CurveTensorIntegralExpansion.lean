/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Kummer.FiniteAdicH1
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicCup
public import Nyll.EtaleCohomology.Classical.AdicCupH1Anticommutativity
public import Nyll.EtaleCohomology.Classical.FiniteLevelScalarApproximation
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.JacobianVarieties.Kummer.CurveNativeAdicH2
public import Nyll.JacobianVarieties.Kummer.CurveNativeCupPairing
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Degree
public import Nyll.JacobianVarieties.Kummer.CurveTensorTrace
public import Nyll.SchemeTheory.RingTheory.LinearAlgebra.TensorScalarExtension
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# An integral expansion of the actual rational negative identity tensor

Clearing one denominator expresses the canonical rational tensor as a
finite sum of original integral H¹ classes. Its original cup contraction
is multiplication by the negative denominator. The same finite family
has that contraction at every original finite coefficient level, because
every finite H¹ class lifts through the actual inverse-limit projection.
No perfectness over the adic integers is needed.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry EtaleCohomology.Classical
open scoped TensorProduct

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

local notation "HZ" => ellAdicCohomology M.C ℓ 1
local notation "HQ" => rationalEllAdicCohomology ℓ M.C 1

/-- The integral cup coefficient acts on an original finite class by
the integer representative of the same finite cup degree. -/
theorem nativeEllAdicCupPairing_projection_smul (n : ℕ) (x y : HZ)
    (z : finiteLevelCohomology M.C ℓ n 1) :
    M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl x y • z =
      (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
        (finiteLevelCup M.C ℓ n 1 1 2 rfl
          (ellAdicProjection M.C ℓ 1 n x) (ellAdicProjection M.C ℓ 1 n y))).val • z := by
  have hdeg := M.nativeEllAdicH2DegreeEquiv_reduction ℓ hℓ
    (ellAdicCup M.C ℓ 1 1 2 rfl x y) n
  rw [ellAdicProjection_cup] at hdeg
  rw [finiteLevelCohomology_smul_eq_appr, ← hdeg]
  change (M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl x y).appr (n + 1) • z =
    ((M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl x y).appr (n + 1) :
      ZMod (ℓ ^ (n + 1))).val • z
  rw [ZMod.val_natCast_of_lt (PadicInt.appr_lt _ _)]

/-- Reversing the original cup factors converts a negative integral
contraction into the positive finite contraction. This is the orientation
of the actual Weil character of a division-cover overlap. -/
theorem nativeFiniteCup_reversed_integral_contraction
    (c : ℤ_[ℓ]) (S : Finset (HZ × HZ))
    (hS : ∀ z : HZ, ∑ v ∈ S,
      M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl z v.2 • v.1 = (-c) • z)
    (n : ℕ) (z : finiteLevelCohomology M.C ℓ n 1) :
    ∑ v ∈ S,
      (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
        (finiteLevelCup M.C ℓ n 1 1 2 rfl
          (ellAdicProjection M.C ℓ 1 n v.2) z)).val •
            ellAdicProjection M.C ℓ 1 n v.1 = c • z := by
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  obtain ⟨w, rfl⟩ := M.ellAdicH1Projection_surjective ℓ hℓ n z
  have hanti (x y : HZ) :
      M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl x y =
        -M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl y x := by
    change M.nativeEllAdicH2DegreeEquiv ℓ hℓ
      (ellAdicCup M.C ℓ 1 1 2 rfl x y) = _
    rw [ellAdicCup_anticomm_one, map_neg]
    rfl
  have hrev : ∑ v ∈ S,
      M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl v.2 w • v.1 = c • w := by
    calc
      (∑ v ∈ S, M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl v.2 w • v.1) =
          ∑ v ∈ S, -(M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl w v.2 • v.1) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hanti, neg_smul]
      _ = -(∑ v ∈ S, M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl w v.2 • v.1) :=
        Finset.sum_neg_distrib (s := S) (fun v : HZ × HZ =>
          M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl w v.2 • v.1)
      _ = c • w := by rw [hS, neg_smul, neg_neg]
  have hproj (a : ℤ_[ℓ]) (x : HZ) :
      ellAdicProjection M.C ℓ 1 n (a • x) =
        a • ellAdicProjection M.C ℓ 1 n x := rfl
  have hp := congrArg (ellAdicProjection M.C ℓ 1 n) hrev
  rw [map_sum, hproj] at hp
  calc
    (∑ v ∈ S,
        (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
          (finiteLevelCup M.C ℓ n 1 1 2 rfl
            (ellAdicProjection M.C ℓ 1 n v.2)
            (ellAdicProjection M.C ℓ 1 n w))).val •
              ellAdicProjection M.C ℓ 1 n v.1) =
        ∑ v ∈ S, ellAdicProjection M.C ℓ 1 n
          (M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl v.2 w • v.1) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [hproj]
      exact (M.nativeEllAdicCupPairing_projection_smul ℓ hℓ n v.2 w
        (ellAdicProjection M.C ℓ 1 n v.1)).symm
    _ = c • ellAdicProjection M.C ℓ 1 n w := hp

/-- One nonzero integral denominator and one finite family represent the
canonical rational negative identity tensor. Their actual cup contractions
are the negative denominator, both integrally and at every finite level. -/
theorem exists_nativeH1_negativeIdentityTensor_integral_expansion :
    ∃ (c : ℤ_[ℓ]) (_ : c ≠ 0) (S : Finset (HZ × HZ)),
      (∑ v ∈ S, ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] v.1) ⊗ₜ[ℚ_[ℓ]]
          ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] v.2)) =
        algebraMap ℤ_[ℓ] ℚ_[ℓ] c • M.nativeRationalH1NegativeIdentityTensor ℓ hℓ ∧
      (∀ z : HZ, ∑ v ∈ S,
          M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl z v.2 • v.1 = (-c) • z) ∧
      (∀ (n : ℕ) (z : finiteLevelCohomology M.C ℓ n 1),
        ∑ v ∈ S,
          (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
            (finiteLevelCup M.C ℓ n 1 1 2 rfl z
              (ellAdicProjection M.C ℓ 1 n v.2))).val •
                ellAdicProjection M.C ℓ 1 n v.1 = (-c) • z) := by
  classical
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  obtain ⟨c, hc, s, hs⟩ :=
    TensorProduct.exists_nonzero_smul_eq_baseChangeTensorMap
      ℤ_[ℓ] ℚ_[ℓ] HZ HZ (M.nativeRationalH1NegativeIdentityTensor ℓ hℓ)
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset s
  rw [hS, map_sum] at hs
  simp only [TensorProduct.baseChangeTensorMap_tmul] at hs
  let : Module ℤ_[ℓ] HQ :=
    inferInstanceAs (Module ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] HZ))
  have : IsScalarTower ℤ_[ℓ] ℚ_[ℓ] HQ :=
    inferInstanceAs (IsScalarTower ℤ_[ℓ] ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] HZ))
  let j : HZ →ₗ[ℤ_[ℓ]] HQ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] HZ 1
  have hsTensor : (∑ v ∈ S, j v.1 ⊗ₜ[ℚ_[ℓ]] j v.2) =
      algebraMap ℤ_[ℓ] ℚ_[ℓ] c • M.nativeRationalH1NegativeIdentityTensor ℓ hℓ := hs
  have hj : Function.Injective j := by
    have : Module.Free ℤ_[ℓ] HZ := (M.finite_free_ellAdicH1 ℓ hℓ).1
    apply (IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors ℤ_[ℓ])
      (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] HZ 1)).mpr
    intro a
    change IsSMulRegular HZ (a : ℤ_[ℓ])
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors (M := HZ) a.2
  have hterm (x y z : HZ) :
      M.nativeRationalH1TensorAction ℓ hℓ (j x ⊗ₜ[ℚ_[ℓ]] j y) (j z) =
        j (M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl z y • x) := by
    rw [nativeRationalH1TensorAction_tmul]
    change M.nativeRationalEllAdicCupPairing ℓ hℓ 1 1 rfl
        ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] z) ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] y) • j x = _
    rw [nativeRationalEllAdicCupPairing_tmul, one_mul, Algebra.smul_def,
      mul_one, algebraMap_smul, j.map_smul]
  have hint (z : HZ) : ∑ v ∈ S,
      M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl z v.2 • v.1 = (-c) • z := by
    apply hj
    calc
      j (∑ v ∈ S, M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl z v.2 • v.1) =
          ∑ v ∈ S, j (M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl z v.2 • v.1) :=
        map_sum j (fun v : HZ × HZ =>
          M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl z v.2 • v.1) S
      _ = M.nativeRationalH1TensorAction ℓ hℓ
          (∑ v ∈ S, j v.1 ⊗ₜ[ℚ_[ℓ]] j v.2) (j z) := by
        rw [map_sum, LinearMap.sum_apply]
        apply Finset.sum_congr rfl
        intro v hv
        exact (hterm v.1 v.2 z).symm
      _ = algebraMap ℤ_[ℓ] ℚ_[ℓ] c • (-j z) := by
        simpa only [map_smul, nativeRationalH1NegativeIdentityTensor_action,
          LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.id_apply] using
          congrArg (fun t : HQ ⊗[ℚ_[ℓ]] HQ =>
            M.nativeRationalH1TensorAction ℓ hℓ t (j z)) hsTensor
      _ = j ((-c) • z) := by
        rw [algebraMap_smul, smul_neg, j.map_smul, neg_smul]
  refine ⟨c, hc, S, hs, hint, ?_⟩
  intro n z
  obtain ⟨v, rfl⟩ := M.ellAdicH1Projection_surjective ℓ hℓ n z
  have hproj (a : ℤ_[ℓ]) (x : HZ) :
      ellAdicProjection M.C ℓ 1 n (a • x) = a • ellAdicProjection M.C ℓ 1 n x := rfl
  have h := congrArg (ellAdicProjection M.C ℓ 1 n) (hint v)
  rw [map_sum, hproj] at h
  calc
    (∑ w ∈ S,
        (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
          (finiteLevelCup M.C ℓ n 1 1 2 rfl (ellAdicProjection M.C ℓ 1 n v)
            (ellAdicProjection M.C ℓ 1 n w.2))).val •
              ellAdicProjection M.C ℓ 1 n w.1) =
        ∑ w ∈ S, ellAdicProjection M.C ℓ 1 n
          (M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl v w.2 • w.1) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [hproj]
      exact (M.nativeEllAdicCupPairing_projection_smul ℓ hℓ n v w.2
        (ellAdicProjection M.C ℓ 1 n w.1)).symm
    _ = (-c) • ellAdicProjection M.C ℓ 1 n v := h

end AlgebraicCurve.CurveModel
