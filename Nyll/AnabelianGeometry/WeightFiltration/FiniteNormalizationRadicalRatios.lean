/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.FiniteNormalizationCharZero
import Nyll.AnabelianGeometry.WeightFiltration.LocalRadicalRatios

/-!
# Actual finite tame evaluation on local radicals

The coefficient unit is constructed from the actual action; it is not supplied
as comparison data. Fixed powers make it a root of unity.
-/

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

universe u v w

/-- The actual localized inertia action fixes the image of the original base ring. -/
theorem finiteNormalizationLocalAction_base
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsPrime]
    (E : FiniteGaloisIntermediateField K L)
    (σ : actualNormalizationInertiaGroup A K L Q) (a : A) :
    let : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
      finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    actualFiniteInertiaLocalRingHom A K L Q E σ
        (algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
          (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
          (algebraMap A (finiteAbsoluteNormalizationAlgebra A K L E) a)) =
      algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
        (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
        (algebraMap A (finiteAbsoluteNormalizationAlgebra A K L E) a) := by
  intro prime
  refine (actualFiniteInertiaLocalRingHom_algebraMap A K L Q E σ
    (algebraMap A (finiteAbsoluteNormalizationAlgebra A K L E) a)).trans ?_
  exact congrArg
    (algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
      (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)))
    (((actualFiniteNormalizationRestriction A K L E).hom
      (actualNormalizationInertiaElement A K L Q σ)).commutes a)

/-- A local radical has its actual inertia ratio evaluated by the original tame coordinate. -/
theorem finiteNormalizationTame_radicalRatio_charZero
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CharZero (IsLocalRing.ResidueField A)] [Field K] [Field L]
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
      ∀ (n : ℕ) (a : A),
        x ^ n = algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
          (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
          (algebraMap A (finiteAbsoluteNormalizationAlgebra A K L E) a) →
      ∃ c : (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))ˣ,
        x * (c : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) =
            actualFiniteInertiaLocalRingHom A K L Q E σ x ∧
          c ^ n = 1 ∧
          actualFiniteLocalResidueMap A K L Q E c =
            (((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val).val ^ m := by
  intro prime dedekind dvr x hx m hm n a hpow
  have hfixed : actualFiniteInertiaLocalRingHom A K L Q E σ (x ^ n) = x ^ n := by
    rw [hpow]
    exact finiteNormalizationLocalAction_base A K L Q E σ a
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
  obtain ⟨d, hd, hπd, _ht⟩ := actualFiniteTameCoordinate_exists_coefficient A K L Q E σ π hπ
  obtain ⟨c, hc⟩ := localUnitRatio_exists
    (actualFiniteInertiaLocalRingHom A K L Q E σ) π hπ hd.unit
    (by rw [hd.unit_spec]; exact hπd) x hx
  exact ⟨c, hc, localUnitRatio_pow_eq_one _ x hx c hc n hfixed,
    finiteNormalizationTame_unitRatio_charZero A K L Q E σ x hx m hm c hc⟩

end AnabelianGeometry.WeightFiltration
