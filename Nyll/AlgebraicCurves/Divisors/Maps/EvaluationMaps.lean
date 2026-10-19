/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.

Adapted Anthropic FLT sources (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_evalFun_algebraMap_pushforward.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_evalFun_pullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.AlgebraicCurves.Divisors.Maps.Maps
import Nyll.AlgebraicCurves.Places.Evaluation.EvalAtAlgebraMapEqEvalAtRestrict
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.Places.Ramification.InertiaDegEqOneIsRational
import Nyll.AlgebraicCurves.Divisors.Maps.MapSupport
import Nyll.AlgebraicCurves.Places.NormTrace.EvalAtNormEqProdFiber
import Nyll.AlgebraicCurves.Places.Restriction.PairwiseDisjointFiber

/-!
# Evaluation Maps
-/

section

/-!
# Divisor eval Fun algebra Map pushforward
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_evalFun_algebraMap_pushforward

open AlgebraicCurve AlgebraicCurve.Divisor

private theorem zpow_finset_sum' {K : Type*} [Field K] {c : K} (hc : c ≠ 0) {ι : Type*}
    (s : Finset ι) (n : ι → ℤ) : ∏ i ∈ s, c ^ n i = c ^ (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, zpow_zero]
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ hc, ih]

theorem _root_.AlgebraicCurve.Divisor.evalFun_algebraMap_pushforward {K F F' : Type*} [Field K]
  [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] {g : F} (hg : g ≠ 0) (D : Divisor K F') (hratw : ∀ w ∈ D.support,
  Place.IsRational w) (hratv : ∀ w ∈ D.support, (w.restrict F).IsRational) (hord : ∀ w ∈ D.support,
  (w.restrict F).ord g = 0) : Divisor.evalFun (algebraMap F F' g) D = Divisor.evalFun g
  (Divisor.pushforward F D) := by
  classical
  have hstep1 : evalFun (algebraMap F F' g) D
      = ∏ w ∈ D.support, (w.restrict F).evalAt g ^ D w := by
    rw [evalFun_def]
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [w.evalAt_algebraMap_eq_evalAt_restrict (hratv w hw)
      ((w.restrict F).mem_of_ord_nonneg hg (hord w hw).ge)]
  have hne : ∀ w ∈ D.support, (w.restrict F).evalAt g ≠ 0 := fun w hw =>
    (w.restrict F).evalAt_ne_zero (hratv w hw) hg (hord w hw)
  have hstep2 : ∏ w ∈ D.support, (w.restrict F).evalAt g ^ D w
      = ∏ v ∈ D.support.image (fun w => w.restrict F),
          ∏ w ∈ D.support with w.restrict F = v, (w.restrict F).evalAt g ^ D w :=
    (Finset.prod_fiberwise_of_maps_to
      (fun w hw => Finset.mem_image.mpr ⟨w, hw, rfl⟩) _).symm
  have hstep3 : ∀ v ∈ D.support.image (fun w => w.restrict F),
      (∏ w ∈ D.support with w.restrict F = v, (w.restrict F).evalAt g ^ D w)
        = v.evalAt g ^ (pushforward F D v) := by
    intro v hv
    obtain ⟨w₀, hw₀, rfl⟩ := Finset.mem_image.mp hv
    calc
      ∏ w ∈ D.support with w.restrict F = w₀.restrict F, (w.restrict F).evalAt g ^ D w
          = ∏ w ∈ D.support with w.restrict F = w₀.restrict F,
              (w₀.restrict F).evalAt g ^ (D w * (w.inertiaDeg F : ℤ)) := by
            refine Finset.prod_congr rfl fun w hw => ?_
            obtain ⟨hwD, hwv⟩ := Finset.mem_filter.mp hw
            rw [hwv, w.inertiaDeg_eq_one_of_isRational (hratw w hwD) (hratv w hwD),
              Nat.cast_one, mul_one]
      _ = (w₀.restrict F).evalAt g
            ^ (∑ w ∈ D.support with w.restrict F = w₀.restrict F,
                D w * (w.inertiaDeg F : ℤ)) :=
            zpow_finset_sum' (hne w₀ hw₀) _ _
      _ = (w₀.restrict F).evalAt g ^ (pushforward F D (w₀.restrict F)) := by
            rw [pushforward_apply, Finset.sum_filter]
  rw [hstep1, hstep2, Finset.prod_congr rfl hstep3]
  exact (Finsupp.prod_of_support_subset _ (support_pushforward_subset D)
    (fun v n => v.evalAt g ^ n) fun v _ => zpow_zero _).symm
end AlgebraicCurves.Divisors.Proofs.Divisor_evalFun_algebraMap_pushforward
end ProofImplementation

end

section

/-!
# Divisor eval Fun pullback
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_evalFun_pullback

open AlgebraicCurve AlgebraicCurve.Divisor

theorem _root_.AlgebraicCurve.Divisor.evalFun_pullback {K F F' : Type*} [Field K] [Field F] [Field
  F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] {f : F'} (hf : f ≠ 0) (E : Divisor K F)
  (hrat : ∀ v ∈ E.support, Place.IsRational v) (hratw : ∀ v ∈ E.support, ∀ w ∈ v.fiber F',
  Place.IsRational w) (hord : ∀ v ∈ E.support, ∀ w ∈ v.fiber F', w.ord f = 0) : Divisor.evalFun f
  (Divisor.pullback F' E) = Divisor.evalFun (Algebra.norm F f) E := by
  classical
  rw [show evalFun f (pullback F' E)
      = ∏ w ∈ E.support.biUnion (fun v => v.fiber F'), w.evalAt f ^ (pullback F' E) w from
    Finsupp.prod_of_support_subset _ (AlgebraicCurve.Divisor.support_pullback_subset E)
      (fun w n => w.evalAt f ^ n) fun w _ => zpow_zero _,
    Finset.prod_biUnion (AlgebraicCurve.Place.pairwiseDisjoint_fiber E.support), evalFun_def]
  refine Finset.prod_congr rfl fun v hv => ?_
  calc
    ∏ w ∈ v.fiber F', w.evalAt f ^ (pullback F' E) w
        = ∏ w ∈ v.fiber F', (w.evalAt f ^ (w.ramificationIndex F : ℤ)) ^ E v := by
          refine Finset.prod_congr rfl fun w hw => ?_
          rw [pullback_apply, Place.mem_fiber.mp hw, ← zpow_mul]
    _ = (∏ w ∈ v.fiber F', w.evalAt f ^ (w.ramificationIndex F : ℤ)) ^ E v :=
          Finset.prod_zpow _ _ _
    _ = (∏ w ∈ v.fiber F', w.evalAt f ^ (w.ramificationIndex F)) ^ E v := by
          refine congrArg (· ^ E v) (Finset.prod_congr rfl fun w _ => ?_)
          rw [zpow_natCast]
    _ = v.evalAt (Algebra.norm F f) ^ E v := by
          rw [AlgebraicCurve.Place.evalAt_norm_eq_prod_fiber v f hf (hrat v hv) (hratw v hv) (hord
            v hv)]
end AlgebraicCurves.Divisors.Proofs.Divisor_evalFun_pullback
end ProofImplementation

end
