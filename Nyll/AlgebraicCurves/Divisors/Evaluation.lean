/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.

The original local additions in the following modules have no established direct
Anthropic source-file match:
- Divisor_evalFun_add
- Divisor_evalFun_mul
- Divisor_evalFun_zpow_left
Anthropic FLT material was identified by code comparison in the following original
modules; their exact source-file correspondence remains unresolved:
- Divisor_evalFun_zsmul
- Divisor_evalFun_single_sub_single
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation

/-!
# Evaluation
-/

section

/-!
Evaluation of a divisor on a sum.
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_evalFun_add

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Divisor.evalFun_add {K F : Type*} [Field K] [Field F] [Algebra K
    F] (f : F) {D E : Divisor K F} (hD : ∀ v ∈ D.support, Place.evalAt v f ≠ 0) (hE : ∀ v ∈
      E.support, Place.evalAt v f ≠ 0) : Divisor.evalFun f (D + E) = Divisor.evalFun f D *
        Divisor.evalFun f E := by
  classical
  refine Finsupp.prod_add_index (fun v _ => zpow_zero _) (fun v hv b₁ b₂ => ?_)
  refine zpow_add₀ ?_ b₁ b₂
  rcases Finset.mem_union.mp hv with h | h
  · exact hD v h
  · exact hE v h
end AlgebraicCurves.Divisors.Proofs.Divisor_evalFun_add
end ProofImplementation

end

section

/-!
Evaluation of a divisor on a product.
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_evalFun_mul

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Divisor.evalFun_mul {K F : Type*} [Field K] [Field F] [Algebra K
    F] {f g : F} {D : Divisor K F} (hrat : ∀ v ∈ D.support, Place.IsRational v) (hf : ∀ v ∈
      D.support, f ∈ v.toValuationSubring) (hg : ∀ v ∈ D.support, g ∈ v.toValuationSubring) :
        Divisor.evalFun (f * g) D = Divisor.evalFun f D * Divisor.evalFun g D := by
  rw [show Divisor.evalFun (f * g) D = D.prod fun v n => v.evalAt f ^ n * v.evalAt g ^ n from
    Finsupp.prod_congr fun v hv => by
      rw [AlgebraicCurve.Place.evalAt_mul v (hrat v hv) (hf v hv) (hg v hv), mul_zpow]]
  exact Finsupp.prod_mul
end AlgebraicCurves.Divisors.Proofs.Divisor_evalFun_mul
end ProofImplementation

end

section

/-!
Evaluate integer powers against divisors.
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_evalFun_zpow_left

open AlgebraicCurve AlgebraicCurve.Divisor

theorem _root_.AlgebraicCurve.Divisor.evalFun_zpow_left {K F : Type*} [Field K] [Field F]
    [Algebra K F] {f : F} (hf : f ≠ 0) {D : Divisor K F} (n : ℤ) (hrat : ∀ v ∈ D.support,
      Place.IsRational v) (hord : ∀ v ∈ D.support, Place.ord v f = 0) : Divisor.evalFun (f ^ n)
        D = Divisor.evalFun f D ^ n := by
  rw [evalFun_def, evalFun_def, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [AlgebraicCurve.Place.evalAt_zpow v (hrat v hv) hf (hord v hv) n, ← zpow_mul, ← zpow_mul,
    mul_comm]
end AlgebraicCurves.Divisors.Proofs.Divisor_evalFun_zpow_left
end ProofImplementation

end

section

/-!
Evaluation of integer multiples of divisors.
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_evalFun_zsmul

open AlgebraicCurve AlgebraicCurve.Divisor

theorem _root_.AlgebraicCurve.Divisor.evalFun_zsmul {K F : Type*} [Field K] [Field F] [Algebra K
    F] (f : F) (D : Divisor K F) (n : ℤ) : Divisor.evalFun f (n • D) = Divisor.evalFun f D ^ n := by
  rw [show evalFun f (n • D) = ∏ v ∈ D.support, v.evalAt f ^ ((n • D) v) from
      Finsupp.prod_of_support_subset _ Finsupp.support_smul _ fun v _ => zpow_zero _,
    evalFun_def, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm n (D v), zpow_mul]
end AlgebraicCurves.Divisors.Proofs.Divisor_evalFun_zsmul
end ProofImplementation

end

section

/-!
Evaluate the difference of two single-point divisors.
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_evalFun_single_sub_single

open AlgebraicCurve AlgebraicCurve.Divisor

theorem _root_.AlgebraicCurve.Divisor.evalFun_single_sub_single {K F : Type*} [Field K] [Field
    F] [Algebra K F] (f : F) {v₁ v₂ : Place K F} (h₁ : v₁.evalAt f ≠ 0) (h₂ : v₂.evalAt f ≠ 0) :
      Divisor.evalFun f (Finsupp.single v₁ 1 + Finsupp.single v₂ (-1)) = v₁.evalAt f / v₂.evalAt
        f := by
  have hsupp : ∀ (w : Place K F) (n : ℤ), w.evalAt f ≠ 0 →
      ∀ v ∈ (Finsupp.single w n).support, Place.evalAt v f ≠ 0 := by
    intro w n hw v hv
    have := Finsupp.support_single_subset hv
    rw [Finset.mem_singleton] at this
    rw [this]
    exact hw
  rw [AlgebraicCurve.Divisor.evalFun_add f (hsupp v₁ 1 h₁) (hsupp v₂ (-1) h₂), evalFun_single,
    evalFun_single,
    zpow_one, zpow_neg_one, div_eq_mul_inv]
end AlgebraicCurves.Divisors.Proofs.Divisor_evalFun_single_sub_single
end ProofImplementation

end
