/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameCoefficientEvaluation

/-!
# Residue fixedness of actual finite normalization inertia

The existing local action and the existing ambient residue map satisfy the
literal residue-fixed square. No replacement action or residue field is used.
-/

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

universe u v w

/-- Actual finite local inertia fixes the image in the original residue field. -/
theorem finiteNormalizationLocalResidue_action
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsPrime]
    (E : FiniteGaloisIntermediateField K L)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    let : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
      finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    ∀ z : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E),
      actualFiniteLocalResidueMap A K L Q E (actualFiniteInertiaLocalRingHom A K L Q E σ z) =
        actualFiniteLocalResidueMap A K L Q E z := by
  intro prime z
  let B := finiteAbsoluteNormalizationAlgebra A K L E
  let P := finiteAbsoluteNormalizationPrime A K L Q E
  let τ := (actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ
  have hj : actualFiniteInertiaLocalRingHom A K L Q E σ =
      (inertiaLocalizationRingEquiv B P τ.val.toRingEquiv τ.property).toRingHom := by
    rw [← actualFiniteInertiaCompositeLocalRingHom_eq A K L Q E σ]
    exact commAlgIdealInertiaLocalRingHom_eq_canonical A B P τ
  have hr := inertiaLocalizationRingEquiv_comp_residue B P τ.val.toRingEquiv τ.property
  rw [actualFiniteLocalResidueMap_eq_residueMap_comp A K L Q E, hj]
  exact congrArg (actualFiniteNormalizationResidueMap A K L Q E)
    (congrArg (fun f : Localization.AtPrime P →+* P.ResidueField => f z) hr)

end AnabelianGeometry.WeightFiltration
