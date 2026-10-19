/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.LocalRadicalValuation
import Nyll.AnabelianGeometry.WeightFiltration.FiniteNormalizationRadicalRatios

/-!
# Radical valuations in actual finite normalizations

The local valuation comparison is instantiated at the original finite
normalization and its actual contracted prime.
-/

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

universe u v w

/-- A finite-normalization radical has the order prescribed by base valuation and ramification. -/
theorem finiteNormalizationRadical_value_relation
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L) :
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
    ∀ a : A, a ≠ 0 →
      ∀ (x : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) (n : ℕ),
        x ^ n = algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
          (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
          (algebraMap A (finiteAbsoluteNormalizationAlgebra A K L E) a) →
        n * (IsDiscreteValuationRing.addVal _ x).toNat =
          (IsDiscreteValuationRing.addVal A a).toNat *
            (finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A := by
  intro prime dedekind dvr a ha x n hpow
  have : (finiteAbsoluteNormalizationPrime A K L Q E).LiesOver
      (IsLocalRing.maximalIdeal A) :=
    subalgebraNormalizationPrime_liesOver_maximalIdeal
      (finiteLevelNormalizationSubalgebra A K L E) Q
  have : Module.IsTorsionFree A (finiteLevelFieldAlgebra A K L E) :=
    .trans_faithfulSMul A K (finiteLevelFieldAlgebra A K L E)
  have : Module.IsTorsionFree A (finiteAbsoluteNormalizationAlgebra A K L E) :=
    inferInstanceAs (Module.IsTorsionFree A (integralClosure A (finiteLevelFieldAlgebra A K L E)))
  exact localRadical_value_relation (finiteAbsoluteNormalizationPrime A K L Q E) a ha x n hpow

end AnabelianGeometry.WeightFiltration
