/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.GenericGaloisMapComparison
import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective

/-! # Surjectivity of the same absolute generic Galois map -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The absolute map used by the actual pointed finite quotients is surjective. -/
theorem absoluteGenericGaloisToFundamentalGroup_surjective
    (U : Scheme.{u}) [IsIntegral U] [IsNormalIntegral U]
    (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω] :
    Function.Surjective (absoluteGenericGaloisToFundamentalGroup U Ω) := by
  rw [absoluteGenericGaloisToFundamentalGroup_eq_fieldSourceAbsoluteGaloisHom]
  let j := U.fromSpecStalk (genericPoint U)
  let : IsDominant j := genericPoint_isDominant U
  let : QuasiCompact j :=
    { isCompact_preimage := fun V _ _ => (Set.toFinite (j ⁻¹' V)).isCompact }
  exact fieldSourceAbsoluteGaloisHom_surjective U.functionField Ω j

end EtaleFundamentalGroups.Inertia
