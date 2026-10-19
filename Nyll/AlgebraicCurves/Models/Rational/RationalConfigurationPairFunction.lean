/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Constants.RatFuncRationalPairConstantExtension
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationBoundaryPlaceOrders

/-! # An arithmetic function for two original rational punctures

Only the original labels are inputs. The actual arithmetic rational places,
the function over k, and its full geometric divisor are all constructed.
The point at infinity is included without any chart restriction.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open AlgebraicCurve
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AlgebraicGeometry.ProjSpace

open AnabelianGeometry.KummerTheory

theorem rationalConfiguration_exists_pair_function
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
    [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]
    (s : Finset (Projectivization k (k × k))) (a b : s) :
    ∃ f : RatFunc k, f ≠ 0 ∧ ∀ W : Place κ (RatFunc κ),
      W.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
        (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
        (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0) := by
  classical
  obtain ⟨V₀, hV₀, hord₀⟩ :=
    rationalConfigurationBoundaryPlace_exists_rationalPlace k κ s a
  obtain ⟨Vinf, hVinf, hordinf⟩ :=
    rationalConfigurationBoundaryPlace_exists_rationalPlace k κ s b
  obtain ⟨f, hf, _, hgeom⟩ :=
    ratFunc_exists_function_geometric_rationalPlace_pair V₀ Vinf hV₀ hVinf
      (rationalConfigurationBoundaryPlace k κ s a).val
      (rationalConfigurationBoundaryPlace k κ s b).val hord₀ hordinf
  exact ⟨f, hf, hgeom⟩

end AlgebraicGeometry.ProjSpace
