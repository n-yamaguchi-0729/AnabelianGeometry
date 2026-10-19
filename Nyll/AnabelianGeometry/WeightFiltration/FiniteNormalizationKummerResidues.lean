/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.FiniteNormalizationKummerEvaluation
import Nyll.AnabelianGeometry.WeightFiltration.FiniteNormalizationBaseCoefficients

/-!
# Base-ring Kummer coefficients and actual tame coordinates

The field-theoretic Kummer ratio, when represented in the original base ring,
is evaluated in the original residue field by the actual finite tame coordinate.
The exponent is constrained by the base valuation and literal ramification index.
-/

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

universe u v w

/-- Evaluate an original base-ring Kummer coefficient through actual finite tame inertia. -/
theorem exists_finiteNormalization_kummerResidue
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CharZero (IsLocalRing.ResidueField A)] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]
    (σ : actualNormalizationInertiaGroup A K L Q)
    (n : ℕ) (hn : 0 < n) (a : A) (β : L) (hβ : β ≠ 0)
    (hpow : β ^ n = algebraMap A L a) (δ : A)
    (hδ : algebraMap A L δ =
      galoisAutomorphismRingHom K L (actualNormalizationInertiaElement A K L Q σ) β / β) :
    ∃ (E : FiniteGaloisIntermediateField K L) (m : ℕ),
      n * m = (IsDiscreteValuationRing.addVal A a).toNat *
        (finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A ∧
      normalizationBaseResidue A L Q δ =
        (((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val).val ^ m := by
  obtain ⟨E, hE⟩ := exists_finiteNormalization_kummerEvaluation A K L Q σ n hn a β hβ hpow
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
  obtain ⟨_x, m, c, _hxb, _hxpow, _hm, hval, _hcn, hc, hres⟩ := hE
  have hbase := finiteNormalizationLocalResidue_eq_base_of_ambient_eq A K L Q E
    c δ (hc.trans hδ.symm)
  exact ⟨E, m, hval, hbase.symm.trans hres⟩

end AnabelianGeometry.WeightFiltration
