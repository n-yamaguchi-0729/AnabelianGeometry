/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.ConstantExtension.PicardNorm
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteConstantsInClosure
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Finite
public import Mathlib.GroupTheory.OrderOfElement
public import Nyll.GaloisCohomology.Cyclic.PeriodicNorm

/-!
# Frobenius fixed vanishing in the actual constant Picard norm system

The actual arithmetic Picard pullback identifies the degree-r constant
model with the classes periodic under the original r-th Frobenius power.
Its degree-zero subgroup is finite by the original Riemann–Roch finiteness
theorem. This constructs the finite fixed subgroup without a rational point,
a chosen Picard representation, or a fixed-vanishing hypothesis.

A family compatible with the actual cyclic norm formulas and fixed by one
positive Frobenius power therefore vanishes. At a stage divisible by that
power, a further norm of length equal to the fixed subgroup's cardinality
is multiplication by that cardinality. Norm compatibility then gives zero
at every preceding stage. The norm formula used here is the one proved for
actual divisor pushforward in `constantPicardBaseChange_norm`.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

namespace CyclicAction

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- A norm-compatible family fixed by one positive power and lying in one
finite subgroup is zero. Only the original cyclic sums occur in the
compatibility relation; no divisibility or vanishing supplier is assumed. -/
theorem normCompatible_fixed_eq_zero_of_finite_subgroup
    (σ : G) (r : ℕ+) (S : AddSubgroup A) [Finite S]
    (x : ℕ+ → A) (hS : ∀ n, x n ∈ S)
    (hnorm : ∀ n m : ℕ+,
      (∑ i ∈ Finset.range (m : ℕ), (σ ^ (n : ℕ)) ^ i • x (n * m)) = x n)
    (hfixed : ∀ n, σ ^ (r : ℕ) • x n = x n) :
    ∀ n, x n = 0 := by
  let N : ℕ+ := ⟨Nat.card S, Nat.card_pos⟩
  intro n
  have hnr : x (n * r) = 0 := by
    have hperiod : σ ^ ((n * r : ℕ+) : ℕ) • x ((n * r) * N) = x ((n * r) * N) := by
      have h := periodicSubgroup_le_mul (A := A) σ (r : ℕ) (n : ℕ)
        (hfixed ((n * r) * N))
      change σ ^ ((r : ℕ) * (n : ℕ)) • x ((n * r) * N) = x ((n * r) * N) at h
      simpa only [PNat.mul_coe, Nat.mul_comm] using h
    have hterm (i : ℕ) :
        (σ ^ ((n * r : ℕ+) : ℕ)) ^ i • x ((n * r) * N) = x ((n * r) * N) := by
      induction i with
      | zero => rw [pow_zero, one_smul]
      | succ i ih => rw [pow_succ', mul_smul, ih, hperiod]
    rw [← hnorm (n * r) N]
    simp only [hterm, Finset.sum_const, Finset.card_range]
    change Nat.card S • x ((n * r) * N) = 0
    exact congrArg Subtype.val
      (card_nsmul_eq_zero' (x := (⟨x ((n * r) * N), hS ((n * r) * N)⟩ : S)))
  rw [← hnorm n r, hnr]
  simp only [smul_zero, Finset.sum_const_zero]

end CyclicAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicCurve.CurveModel

attribute [local instance]
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0

variable {k Ω : Type uGeom} {F₀ : Type uField₁} {F : Type uField₂}
  [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
  [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
  [Field F₀] [Algebra k F₀] [IsCurveOver k F₀] [Algebra.EssFiniteType k F₀]
  [Field F] [Algebra Ω F] [IsCurveOver Ω F]
  (M₀ : CurveModel k F₀) [GeometricallyIntegral M₀.toBase]
  (M : CurveModel Ω F) (e : M.C ≅ pullback M₀.toBase (specMap k Ω))
  (he : e.hom ≫ pullback.snd M₀.toBase (specMap k Ω) = M.toBase)

local notation "φ" => M.constantSemilinearAction M₀.toBase e he
  (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)

/-- The degree-zero classes fixed by the original geometric Frobenius power. -/
def constantPicardZeroFixedSubgroup (r : ℕ) : AddSubgroup (Pic Ω F) :=
  (H1Gm.degree Ω F).ker ⊓ CyclicAction.periodicSubgroup (A := Pic Ω F) φ r

omit [IsCurveOver k F₀] [Algebra.EssFiniteType k F₀] in
/-- The original positive-power fixed degree-zero subgroup is finite.
Actual finite-constant Picard descent and Riemann–Roch provide its finite
target; no pointed curve or abstract Picard comparison is an input. -/
theorem finite_constantPicardZeroFixedSubgroup (r : ℕ) (hr : r ≠ 0) :
    Finite (M₀.constantPicardZeroFixedSubgroup M e he r) := by
  have : NeZero r := ⟨hr⟩
  let E : Type uGeom := FunctionField.finiteConstantsInClosure k Ω r
  have : Finite E := FunctionField.finite_finiteConstantsInClosure k Ω r
  let : Fintype E := Fintype.ofFinite E
  have : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := k) E
  have hd : Module.finrank k E = r := FunctionField.finrank_finiteConstantsInClosure k Ω r
  let CE := pullback M₀.toBase (specMap k E)
  let cE := pullback.snd M₀.toBase (specMap k E)
  let : Algebra E CE.functionField := (baseToFunctionField cE).toAlgebra
  have : IsCurveOver E CE.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one cE
      (RingEquiv.refl _) (fun _ => rfl)
  have : Algebra.EssFiniteType E CE.functionField := essFiniteType_functionField cE
  let ME : CurveModel E CE.functionField := ofSmoothProperCurve cE
  let eE := M.constantTowerModelIso k E Ω M₀.toBase e
  have heE := M.constantTowerModelIso_base k E Ω M₀.toBase e he
  have hC : ConstantsAreBase E CE.functionField :=
    ME.constantsAreBase_of_constantModel M eE heE
  have : Finite (Pic0 E CE.functionField) := finite_pic0_of_isCurveOver E CE.functionField hC
  have : Finite (H1Gm.degree E CE.functionField).ker :=
    Finite.of_injective (H1Gm.ofPic0Equiv E CE.functionField).symm
      (H1Gm.ofPic0Equiv E CE.functionField).symm.injective
  let P := M₀.constantPicardPeriodicEquiv M e he E
  let intoPeriod (a : M₀.constantPicardZeroFixedSubgroup M e he r) :
      CyclicAction.periodicSubgroup (A := Pic Ω F) φ (Module.finrank k E) :=
    ⟨a.val, by
      change φ ^ Module.finrank k E • a.val = a.val
      rw [hd]
      exact a.property.2⟩
  let f : M₀.constantPicardZeroFixedSubgroup M e he r →
      (H1Gm.degree E CE.functionField).ker := fun a =>
    ⟨P.symm (intoPeriod a), by
      have hdegree := M₀.degree_constantPicardPeriodicEquiv M e he E
        (P.symm (intoPeriod a))
      change H1Gm.degree Ω F (P (P.symm (intoPeriod a)) : Pic Ω F) =
        H1Gm.degree E CE.functionField (P.symm (intoPeriod a)) at hdegree
      rw [P.apply_symm_apply] at hdegree
      exact hdegree.symm.trans a.property.1⟩
  apply Finite.of_injective f
  intro a b hab
  apply Subtype.ext
  have hab' : P.symm (intoPeriod a) = P.symm (intoPeriod b) :=
    congrArg (fun z : (H1Gm.degree E CE.functionField).ker => z.val) hab
  exact congrArg
    (fun z : CyclicAction.periodicSubgroup (A := Pic Ω F) φ (Module.finrank k E) => z.val)
    (P.symm.injective hab')

/-- On a class already fixed by the original Frobenius, the actual finite
constant norm is multiplication by the extension degree after original
geometric pullback. The norm is actual divisor pushforward. -/
theorem constantPicardBaseChange_norm_eq_nsmul_of_fixed
    (E : Type uGeom) [Field E] [Fintype E] [Algebra k E] [Algebra E Ω]
    [IsScalarTower k E Ω] [Algebra.IsAlgebraic E Ω] :
    let CE := pullback M₀.toBase (specMap k E)
    let cE := pullback.snd M₀.toBase (specMap k E)
    let _ : Algebra E CE.functionField := (baseToFunctionField cE).toAlgebra
    ∀ x : Pic E CE.functionField,
      φ • (M₀.constantPicardPeriodicEquiv M e he E x : Pic Ω F) =
        (M₀.constantPicardPeriodicEquiv M e he E x : Pic Ω F) →
      M₀.constantPicardBaseChange M e he (M₀.constantPicardNorm M e he E x) =
        Module.finrank k E • (M₀.constantPicardPeriodicEquiv M e he E x : Pic Ω F) := by
  intro CE cE algE x hx
  rw [M₀.constantPicardBaseChange_norm M e he E]
  have hpow (i : ℕ) : φ ^ i • (M₀.constantPicardPeriodicEquiv M e he E x : Pic Ω F) =
      (M₀.constantPicardPeriodicEquiv M e he E x : Pic Ω F) := by
    induction i with
    | zero => rw [pow_zero, one_smul]
    | succ i ih => rw [pow_succ', mul_smul, ih, hx]
  simp only [hpow, Finset.sum_const, Finset.card_range]

omit [IsCurveOver k F₀] [Algebra.EssFiniteType k F₀] in
/-- A family of actual geometric divisor classes compatible with the
constant-stage norm formulas has no nonzero degree-zero Frobenius-fixed
element. The finite fixed subgroup is constructed from actual Picard descent. -/
theorem picard_normCompatible_zeroDegree_fixed_eq_zero
    (x : ℕ+ → Pic Ω F) (hdegree : ∀ n, H1Gm.degree Ω F (x n) = 0)
    (hnorm : ∀ n m : ℕ+,
      (∑ i ∈ Finset.range (m : ℕ), (φ ^ (n : ℕ)) ^ i • x (n * m)) = x n)
    (r : ℕ) (hr : r ≠ 0) (hfixed : ∀ n, φ ^ r • x n = x n) :
    ∀ n, x n = 0 := by
  have : Finite (M₀.constantPicardZeroFixedSubgroup M e he r) :=
    M₀.finite_constantPicardZeroFixedSubgroup M e he r hr
  exact CyclicAction.normCompatible_fixed_eq_zero_of_finite_subgroup
    φ ⟨r, Nat.pos_of_ne_zero hr⟩ (M₀.constantPicardZeroFixedSubgroup M e he r) x
    (fun n => ⟨hdegree n, hfixed n⟩) hnorm hfixed

omit [IsCurveOver k F₀] [Algebra.EssFiniteType k F₀] in
/-- The same fixed-vanishing theorem on the original `Pic0`, retaining all
prime-primary parts. Its embedding in the full Picard group is the original
degree exact sequence, so no Tate comparison or torsion-freeness is assumed. -/
theorem pic0_normCompatible_fixed_eq_zero
    (x : ℕ+ → Pic0 Ω F)
    (hnorm : ∀ n m : ℕ+,
      (∑ i ∈ Finset.range (m : ℕ), (φ ^ (n : ℕ)) ^ i • x (n * m)) = x n)
    (r : ℕ) (hr : r ≠ 0) (hfixed : ∀ n, φ ^ r • x n = x n) :
    ∀ n, x n = 0 := by
  have h := M₀.picard_normCompatible_zeroDegree_fixed_eq_zero M e he
    (fun n => H1Gm.ofPic0 Ω F (x n)) (fun n => H1Gm.degree_ofPic0 Ω F (x n))
    (fun n m => by
      simpa only [map_sum, H1Gm.ofPic0_smul] using
        congrArg (H1Gm.ofPic0 Ω F) (hnorm n m)) r hr
    (fun n => by
      rw [← H1Gm.ofPic0_smul, hfixed])
  intro n
  apply H1Gm.ofPic0_injective Ω F
  rw [map_zero]
  exact h n

end AlgebraicCurve.CurveModel
