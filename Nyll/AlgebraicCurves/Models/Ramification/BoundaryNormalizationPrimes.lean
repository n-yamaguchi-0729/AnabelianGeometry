/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Models.Ramification.OpenBoundary
import Nyll.EtaleFundamentalGroups.Inertia.PlaceNormalizationInertiaRestriction

/-! # An actual normalization-prime family at all boundary places

The ambient field and each boundary place are fixed. Ordinary maximal-ideal
existence chooses a prime in that place's actual normalization, supplying the
prime-family parameter without an additional geometric hypothesis.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve SchemeTheory

namespace AlgebraicCurve.CurveModel

attribute [local instance] EtaleFundamentalGroups.Inertia.placeBaseAmbientAlgebra
  EtaleFundamentalGroups.Inertia.placeBaseAmbientTower

variable {κ F Ω : Type} [Field κ] [Field F] [Algebra κ F]
    [Field Ω] [Algebra F Ω]
    (M : CurveModel κ F) {X : Scheme} (j : X ⟶ M.C)

/-- A maximal ideal of the normalization at each original boundary place. -/
def boundaryNormalizationPrimes (p : M.openBoundaryPlaces j) :
    Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω) := by
  let : Nontrivial (normalizationCommAlgCat p.val.toValuationSubring Ω) :=
    (inferInstance : Nontrivial (integralClosure p.val.toValuationSubring Ω))
  exact Classical.choose (Ideal.exists_maximal
    (normalizationCommAlgCat p.val.toValuationSubring Ω))

/-- Every chosen ideal has the maximality required by actual cusp recognition. -/
instance boundaryNormalizationPrimes_isMaximal (p : M.openBoundaryPlaces j) :
    (M.boundaryNormalizationPrimes (Ω := Ω) j p).IsMaximal := by
  let : Nontrivial (normalizationCommAlgCat p.val.toValuationSubring Ω) :=
    (inferInstance : Nontrivial (integralClosure p.val.toValuationSubring Ω))
  exact Classical.choose_spec (Ideal.exists_maximal
    (normalizationCommAlgCat p.val.toValuationSubring Ω))

end AlgebraicCurve.CurveModel
