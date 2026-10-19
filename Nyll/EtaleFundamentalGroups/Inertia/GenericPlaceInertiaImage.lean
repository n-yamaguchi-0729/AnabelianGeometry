/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.GenericGaloisMapComparison

/-!
# Original place inertia as the actual absolute Galois image

This comparison keeps the original normalization prime and geometric point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve SchemeTheory
open EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] normalizationCommAlgGaloisAction

/-- At the literal function field, the two actual inertia images coincide. -/
theorem genericPlaceInertia_eq_absoluteInertiaImage
    {k : Type} [Field k] (U : Scheme) [IsIntegral U]
    [Algebra k U.functionField]
    {Ω : Type} [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    (p : Place k U.functionField) [Algebra p.toValuationSubring Ω]
    [IsScalarTower p.toValuationSubring U.functionField Ω]
    (Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω)) :
    genericPlaceInertia U p Q =
      (Q.inertia Gal(Ω/U.functionField)).map
        (absoluteGenericGaloisToFundamentalGroup U Ω) := by
  rw [← genericPlaceInertiaHom_range U p Q Function.surjective_id]
  ext g
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨τ.val, τ.property,
      (genericPlaceInertiaHom_eq_absoluteGenericGalois U p Q τ).symm⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, hσ⟩, genericPlaceInertiaHom_eq_absoluteGenericGalois U p Q ⟨σ, hσ⟩⟩

end AnabelianGeometry.WeightFiltration
