/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineBoundaryPlaces
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationCuspPlaces

/-! # Rational orders at each specified actual boundary place

The rational-section construction is identified with the place of the same
original label by the proved singleton fiber. The second export quantifies
over every geometric boundary place; it does not select unrelated points.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AlgebraicGeometry.ProjSpace

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
    [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]

/-- Exact normalized order compatibility at the place of a specified original label. -/
theorem rationalConfigurationBoundaryPlace_exists_rationalPlace
    (s : Finset (Projectivization k (k × k))) (a : s) :
    ∃ V : Place k (RatFunc k), V.IsRational ∧
      ∀ z : RatFunc k,
        (rationalConfigurationBoundaryPlace k κ s a).val.ord
          (algebraMap (RatFunc k) (RatFunc κ) z) = V.ord z := by
  obtain ⟨V, hV, p, hcenter, hord⟩ :=
    rationalConfiguration_exists_rational_boundaryPlace k κ s a.val a.property
  have hp : p = rationalConfigurationBoundaryPlace k κ s a := by
    apply Subtype.ext
    apply (projectiveLineRatFuncModel κ).placeEquiv.symm.injective
    apply Subtype.ext
    have hc := (map_eq_projectiveRationalPoint_iff k κ a.val
      ((projectiveLineRatFuncModel κ).placeEquiv.symm p.val).val).mp hcenter
    exact hc.trans (rationalConfigurationBoundaryPlace_center k κ s a).symm
  exact ⟨V, hV, hp ▸ hord⟩

/-- Every actual geometric boundary place restricts with unchanged normalized
order to a rational arithmetic place, including the point at infinity. -/
theorem rationalConfiguration_every_boundaryPlace_exists_rationalPlace
    (s : Finset (Projectivization k (k × k)))
    (p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s)) :
    ∃ V : Place k (RatFunc k), V.IsRational ∧
      ∀ z : RatFunc k,
        p.val.ord (algebraMap (RatFunc k) (RatFunc κ) z) = V.ord z := by
  obtain ⟨a, ha⟩ := (rationalConfigurationBoundaryPlaceEquiv k κ s).surjective p
  obtain ⟨V, hV, hord⟩ :=
    rationalConfigurationBoundaryPlace_exists_rationalPlace k κ s a
  have ha' : rationalConfigurationBoundaryPlace k κ s a = p := ha
  exact ⟨V, hV, ha' ▸ hord⟩

end AlgebraicGeometry.ProjSpace
