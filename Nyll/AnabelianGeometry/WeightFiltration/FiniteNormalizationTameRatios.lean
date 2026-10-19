/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.LocalCoefficientRatios
import Nyll.AnabelianGeometry.WeightFiltration.FiniteNormalizationResidueAction

/-!
# Actual finite tame coordinates on arbitrary local elements

The original finite tame coordinate evaluates unit ratios of nonzero local
elements by their normalized valuation. Both the local action and the residue
map are the existing finite-normalization maps.
-/

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

universe u v w

/-- Unit ratios under actual normalization inertia recover powers of the actual tame coordinate. -/
theorem finiteNormalizationTame_unitRatio
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    let : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
      finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    let : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E) :=
      finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
    let : IsDiscreteValuationRing
        (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) :=
      localizationAtPrime_isDiscreteValuationRing
        (finiteAbsoluteNormalizationAlgebra A K L E)
        (finiteAbsoluteNormalizationPrime A K L Q E)
        (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)
    ∀ (x : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)), x ≠ 0 →
      ∀ m : ℕ, IsDiscreteValuationRing.addVal _ x = m →
      ∀ c : (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))ˣ,
        x * (c : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) =
          actualFiniteInertiaLocalRingHom A K L Q E σ x →
        (actualFiniteLocalResidueMap A K L Q E c) ^
            ((finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A /
              actualFiniteStageTameOrder A K L Q E) =
          (((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val).val ^ m := by
  intro prime dedekind dvr x hx m hm c hc
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
  obtain ⟨d, _hd, hπd, ht⟩ := actualFiniteTameCoordinate_exists_coefficient A K L Q E σ π hπ
  have hr := localCoefficientRatio_residue_of_addVal
    (actualFiniteLocalResidueMap A K L Q E) (actualFiniteInertiaLocalRingHom A K L Q E σ)
    (finiteNormalizationLocalResidue_action A K L Q E σ) π hπ d hπd x hx m hm c hc
  rw [hr, ht, ← pow_mul, ← pow_mul, Nat.mul_comm m]
  rfl

end AnabelianGeometry.WeightFiltration
