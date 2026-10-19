/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.FiniteNormalizationLocalAmbient
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteLocalResidue

/-!
# Base coefficients in actual finite local normalizations

An ambient coefficient which comes from the original base ring has the same
residue through the actual finite local map and the original normalization.
-/

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

universe u v w

/-- The original base map to the residue field of the chosen normalization prime. -/
def normalizationBaseResidue
    (A : Type u) (L : Type w) [CommRing A] [Field L] [Algebra A L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsPrime] : A →+* Q.ResidueField :=
  (IsLocalRing.residue (Localization.AtPrime Q)).comp
    ((algebraMap (normalizationCommAlgCat A L) (Localization.AtPrime Q)).comp
      (algebraMap A (normalizationCommAlgCat A L)))

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsPrime]
  (E : FiniteGaloisIntermediateField K L)

/-- The local ambient embedding retains the original base-ring map. -/
theorem finiteNormalizationLocalAmbient_base (a : A) :
    let : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
      finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    finiteNormalizationLocalAmbient A K L Q E
        (algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
          (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
          (algebraMap A (finiteAbsoluteNormalizationAlgebra A K L E) a)) =
      algebraMap A L a := by
  intro prime
  exact finiteNormalizationLocalAmbient_algebraMap A K L Q E
    (algebraMap A (finiteAbsoluteNormalizationAlgebra A K L E) a)

/-- The actual finite residue map retains the original base residue map. -/
theorem finiteNormalizationLocalResidue_base (a : A) :
    let : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
      finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    actualFiniteLocalResidueMap A K L Q E
        (algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
          (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
          (algebraMap A (finiteAbsoluteNormalizationAlgebra A K L E) a)) =
      normalizationBaseResidue A L Q a := by
  intro prime
  exact congrArg (IsLocalRing.residue (Localization.AtPrime Q))
    (Localization.localRingHom_to_map (finiteAbsoluteNormalizationPrime A K L Q E) Q
      (finiteAbsoluteNormalizationRingMap A K L E) rfl
      (algebraMap A (finiteAbsoluteNormalizationAlgebra A K L E) a))

/-- An actual local coefficient with a prescribed base-ring image has that base residue. -/
theorem finiteNormalizationLocalResidue_eq_base_of_ambient_eq :
    let : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
      finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    ∀ (c : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) (a : A),
      finiteNormalizationLocalAmbient A K L Q E c = algebraMap A L a →
      actualFiniteLocalResidueMap A K L Q E c = normalizationBaseResidue A L Q a := by
  intro prime c a h
  have hc : c = algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
      (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))
      (algebraMap A (finiteAbsoluteNormalizationAlgebra A K L E) a) :=
    finiteNormalizationLocalAmbient_injective A K L Q E
      (h.trans (finiteNormalizationLocalAmbient_base A K L Q E a).symm)
  rw [hc]
  exact finiteNormalizationLocalResidue_base A K L Q E a

end AnabelianGeometry.WeightFiltration
