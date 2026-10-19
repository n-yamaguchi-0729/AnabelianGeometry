/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Rational.ProjectiveRatFuncPairEvaluation
import Nyll.AlgebraicCurves.Places.Evaluation.SemilinearEvaluation

/-! # Semilinear cross ratios of the actual rational-function places

The comparison uses the actual pair function, its orders, and residue
evaluation. No classification of rational-function automorphisms and no
assumed projective formula for the semilinear place action is used.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open AlgebraicCurve
open AnabelianGeometry.ProjectiveLine
open scoped RatFunc

namespace AnabelianGeometry.WeightFiltration

variable {K : Type*} [Field K]

/-- The public divisor-evaluation formula, specialized to a single point. -/
theorem evalAt_semilinear_of_mem
    {F : Type*} [Field F] [Algebra K F]
    (g : SemilinearAut K F) (v : Place K F) (hv : v.IsRational)
    (f : F) (hf : f ∈ v.toValuationSubring) :
    (g • v).evalAt (g • f) = SemilinearAut.baseAut g (v.evalAt f) := by
  classical
  have hrat : ∀ w ∈ (Finsupp.single v (1 : ℤ)).support, Place.IsRational w := by
    intro w hw
    obtain ⟨rfl, _⟩ := (Finsupp.mem_support_single w v (1 : ℤ)).mp hw
    exact hv
  have hmem : ∀ w ∈ (Finsupp.single v (1 : ℤ)).support, f ∈ w.toValuationSubring := by
    intro w hw
    obtain ⟨rfl, _⟩ := (Finsupp.mem_support_single w v (1 : ℤ)).mp hw
    exact hf
  simpa only [SemilinearAut.smul_single, Divisor.evalFun_single, zpow_one] using
    SemilinearAut.evalFun_smul g (Finsupp.single v (1 : ℤ)) hrat hmem

private theorem crossRatio_second_third (a b d : Projectivization K (K × K)) :
    crossRatio a b b d = 0 := by
  have hb : bracket b.rep b.rep = 0 := by
    unfold bracket
    ring
  simp only [crossRatio, homogeneousCrossRatio, hb, mul_zero, zero_div]

private theorem crossRatio_second_fourth (a b c : Projectivization K (K × K)) :
    crossRatio a b c b = 0 := by
  have hb : bracket b.rep b.rep = 0 := by
    unfold bracket
    ring
  simp only [crossRatio, homogeneousCrossRatio, hb, zero_mul, div_zero]

/-- Any permutation realized by the actual semilinear place action transforms
the cross ratio by the same automorphism of the constant field. -/
theorem crossRatio_of_semilinear_places
    (g : SemilinearAut K (RatFunc K))
    (τ : Equiv.Perm (Projectivization K (K × K)))
    (hτ : ∀ p, projectiveRatFuncPlace (τ p) = g • projectiveRatFuncPlace p)
    (a b c d : Projectivization K (K × K)) :
    crossRatio (τ a) (τ b) (τ c) (τ d) =
      SemilinearAut.baseAut g (crossRatio a b c d) := by
  classical
  by_cases hcb : c = b
  · subst c
    rw [crossRatio_second_third, crossRatio_second_third, map_zero]
  by_cases hdb : d = b
  · subst d
    rw [crossRatio_second_fourth, crossRatio_second_fourth, map_zero]
  let f : RatFunc K := pairRatFunc a b
  have hf : f ≠ 0 := div_ne_zero
    (pairLinearRatFunc_ne_zero a.rep a.rep_nonzero)
    (pairLinearRatFunc_ne_zero b.rep b.rep_nonzero)
  have hgf : g • f ≠ 0 := by
    intro h
    apply hf
    have hh := congrArg (fun z : RatFunc K => g⁻¹ • z) h
    simpa only [inv_smul_smul, smul_zero] using hh
  have horders (V : Place K (RatFunc K)) :
      V.ord (g • f) = (if V = projectiveRatFuncPlace (τ a) then 1 else 0) -
        (if V = projectiveRatFuncPlace (τ b) then 1 else 0) := by
    have heq (p : Projectivization K (K × K)) :
        g⁻¹ • V = projectiveRatFuncPlace p ↔ V = projectiveRatFuncPlace (τ p) := by
      rw [hτ p]
      constructor
      · intro h
        exact (smul_inv_smul g V).symm.trans (congrArg (fun w => g • w) h)
      · intro h
        rw [h, inv_smul_smul]
    have h := SemilinearAut.ord_smul g (g⁻¹ • V) f
    rw [smul_inv_smul] at h
    rw [h, pairRatFunc_orders, heq a, heq b]
  have hmem (p : Projectivization K (K × K)) (hp : p ≠ b) :
      f ∈ (projectiveRatFuncPlace p).toValuationSubring := by
    apply (projectiveRatFuncPlace p).mem_of_ord_nonneg hf
    rw [pairRatFunc_orders, ite_eq_right (projectiveRatFuncPlace_injective.ne hp), sub_zero]
    split_ifs <;> omega
  calc
    crossRatio (τ a) (τ b) (τ c) (τ d) =
        (projectiveRatFuncPlace (τ d)).evalAt (g • f) /
          (projectiveRatFuncPlace (τ c)).evalAt (g • f) :=
      (ratFunc_pair_evalAt_ratio_eq_crossRatio (τ a) (τ b) (τ c) (τ d)
        (τ.injective.ne hcb) (τ.injective.ne hdb) (g • f) hgf horders).symm
    _ = SemilinearAut.baseAut g
        ((projectiveRatFuncPlace d).evalAt f / (projectiveRatFuncPlace c).evalAt f) := by
      rw [hτ d, hτ c,
        evalAt_semilinear_of_mem g _ (projectiveRatFuncPlace_isRational d) f (hmem d hdb),
        evalAt_semilinear_of_mem g _ (projectiveRatFuncPlace_isRational c) f (hmem c hcb),
        map_div₀]
    _ = SemilinearAut.baseAut g (crossRatio a b c d) :=
      congrArg (SemilinearAut.baseAut g)
        (ratFunc_pair_evalAt_ratio_eq_crossRatio a b c d hcb hdb f hf
          (pairRatFunc_orders a b))

/-- The place formula can be read from any homogeneous representative. -/
theorem projectiveRatFuncPlace_mk_coordinates (v : K × K) (hv : v ≠ 0) :
    projectiveRatFuncPlace (Projectivization.mk K v hv) =
      if v.2 = 0 then RationalFunctionField.placeInfty K
        else RationalFunctionField.placeOfPoint K (v.1 / v.2) := by
  classical
  obtain ⟨t, ht⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  unfold projectiveRatFuncPlace
  rw [← ht]
  change (if (t : K) * v.2 = 0 then RationalFunctionField.placeInfty K
      else RationalFunctionField.placeOfPoint K (((t : K) * v.1) / ((t : K) * v.2))) = _
  by_cases h : v.2 = 0
  · simp only [h, mul_zero, ite_true]
  · rw [ite_eq_right (mul_ne_zero t.ne_zero h), ite_eq_right h, mul_div_mul_left _ _ t.ne_zero]

/-- Over an algebraically closed field, projective coordinates label every
actual rational-function place, including infinity. -/
theorem projectiveRatFuncPlace_bijective [IsAlgClosed K] :
    Function.Bijective (projectiveRatFuncPlace (k := K)) := by
  classical
  refine ⟨projectiveRatFuncPlace_injective, ?_⟩
  intro V
  rcases RationalFunctionField.eq_placeOfPoint_or_eq_placeInfty K V with ⟨a, ha⟩ | ha
  · have hv : (a, (1 : K)) ≠ 0 := by
      intro h
      exact one_ne_zero (congrArg Prod.snd h)
    refine ⟨Projectivization.mk K (a, 1) hv, ?_⟩
    rw [projectiveRatFuncPlace_mk_coordinates, ite_eq_right one_ne_zero, div_one]
    exact ha.symm
  · have hv : ((1 : K), (0 : K)) ≠ 0 := by
      intro h
      exact one_ne_zero (congrArg Prod.fst h)
    refine ⟨Projectivization.mk K (1, 0) hv, ?_⟩
    rw [projectiveRatFuncPlace_mk_coordinates, ite_eq_left rfl]
    exact ha.symm

/-- The permutation of projective points induced by the actual place action. -/
def projectivePointSemilinearEquiv [IsAlgClosed K]
    (g : SemilinearAut K (RatFunc K)) : Equiv.Perm (Projectivization K (K × K)) :=
  let e := Equiv.ofBijective projectiveRatFuncPlace (projectiveRatFuncPlace_bijective (K := K))
  (e.trans (MulAction.toPerm g)).trans e.symm

/-- The constructed point permutation has the required literal place map. -/
theorem projectivePointSemilinearEquiv_place [IsAlgClosed K]
    (g : SemilinearAut K (RatFunc K)) (p : Projectivization K (K × K)) :
    projectiveRatFuncPlace (projectivePointSemilinearEquiv g p) =
      g • projectiveRatFuncPlace p :=
  (Equiv.ofBijective projectiveRatFuncPlace
    (projectiveRatFuncPlace_bijective (K := K))).apply_symm_apply _

/-- The actual geometric semilinear action on all projective points obeys
the cross-ratio coefficient formula, without an assumed coordinate action. -/
theorem crossRatio_projectivePointSemilinearEquiv [IsAlgClosed K]
    (g : SemilinearAut K (RatFunc K))
    (a b c d : Projectivization K (K × K)) :
    crossRatio (projectivePointSemilinearEquiv g a) (projectivePointSemilinearEquiv g b)
      (projectivePointSemilinearEquiv g c) (projectivePointSemilinearEquiv g d) =
      SemilinearAut.baseAut g (crossRatio a b c d) :=
  crossRatio_of_semilinear_places g (projectivePointSemilinearEquiv g)
    (projectivePointSemilinearEquiv_place g) a b c d

end AnabelianGeometry.WeightFiltration
