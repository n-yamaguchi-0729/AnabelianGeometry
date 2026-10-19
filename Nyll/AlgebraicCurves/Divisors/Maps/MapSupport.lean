/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).

The original local additions in the following modules have no established direct
Anthropic source-file match:
- Divisor_support_pullback_subset
- Divisor_support_pushforward_subset
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

import Nyll.AlgebraicCurves.Divisors.Maps.Maps

/-!
# Map Support
-/

section

/-!
# Divisor support pullback subset
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_support_pullback_subset

open AlgebraicCurve AlgebraicCurve.Divisor

theorem _root_.AlgebraicCurve.Divisor.support_pullback_subset {K F F' : Type*} [Field K] [Field F]
  [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral
  F F'] [HasPrincipalDivisors K F'] [DecidableEq (Place K F')] (E : Divisor K F) :
  (Divisor.pullback F' E).support ⊆ E.support.biUnion (fun v => v.fiber F') := by
  classical
  intro w hw
  exact Finset.mem_biUnion.mpr ⟨w.restrict F,
    restrict_mem_support_of_mem_support_pullback hw, w.restrict_mem_fiber⟩
end AlgebraicCurves.Divisors.Proofs.Divisor_support_pullback_subset
end ProofImplementation

end

section

/-!
# Divisor support pushforward subset
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_support_pushforward_subset

open AlgebraicCurve AlgebraicCurve.Divisor

theorem _root_.AlgebraicCurve.Divisor.support_pushforward_subset {K F F' : Type*} [Field K] [Field
  F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [DecidableEq (Place K F)] (D : Divisor K F') : (Divisor.pushforward F
  D).support ⊆ D.support.image (fun w => w.restrict F) := by
  classical
  intro v hv
  rw [Finsupp.mem_support_iff, pushforward_apply] at hv
  obtain ⟨w, hw, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  refine Finset.mem_image.mpr ⟨w, hw, ?_⟩
  by_contra h
  exact hne (ite_eq_right h)
end AlgebraicCurves.Divisors.Proofs.Divisor_support_pushforward_subset
end ProofImplementation

end
