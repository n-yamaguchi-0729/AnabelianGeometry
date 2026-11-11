/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.CartierAdicCycleClass
public import Nyll.EtaleCohomology.Classical.CartierAdicCyclePullback
public import Nyll.EtaleCohomology.Classical.DiagonalPointSectionIdeals
public import Nyll.EtaleCohomology.Classical.GraphAdicCycleClass
public import Nyll.EtaleCohomology.Classical.GraphCartierCycleClass
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalKunnethSections
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Original diagonal classes on the actual point sections

The genuine Cartesian intersection with either point section identifies
the pulled diagonal ideal with the original point ideal. Original
Cartier cycle pullback therefore gives the actual point class, first at
each finite level and then in the original integral and rational groups.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open EtaleCohomology.Classical
open scoped TensorProduct

namespace EtaleCohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (.of K)) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  [IsIntegral (pullback f f)]
  (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

private theorem finiteDiagonalCycleClass_pointSection
    (t : X ⟶ pullback f f) (ht : t ≫ (pullback.snd f f ≫ f) = f)
    (hI : (graphOver f (𝟙 X) (Category.id_comp f)).ker.comap t = p.ker)
    (n : ℕ) :
    finiteLevelCohomologyPullback ℓ t n 2
        (finiteGraphCycleClass f f (𝟙 X) (Category.id_comp f) ℓ hℓ n) =
      finiteEffectiveCartierCycleClass f ℓ hℓ n
        (sectionEffectiveCartierDivisor f p hp) := by
  let D := graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)
  have hD : (D.1.comap t).IsEffectiveCartier := by
    change ((graphOver f (𝟙 X) (Category.id_comp f)).ker.comap t).IsEffectiveCartier
    rw [hI]
    exact (sectionEffectiveCartierDivisor f p hp).2
  have hpoint : (⟨D.1.comap t, hD⟩ : Scheme.EffectiveCartierDivisor X) =
      sectionEffectiveCartierDivisor f p hp := Subtype.ext hI
  calc
    finiteLevelCohomologyPullback ℓ t n 2
        (finiteGraphCycleClass f f (𝟙 X) (Category.id_comp f) ℓ hℓ n) =
        finiteEffectiveCartierCycleClass (t ≫ (pullback.snd f f ≫ f)) ℓ hℓ n
          ⟨D.1.comap t, hD⟩ :=
      finiteEffectiveCartierCycleClass_pullback t (pullback.snd f f ≫ f) ℓ hℓ n D hD
    _ = finiteEffectiveCartierCycleClass f ℓ hℓ n
        (sectionEffectiveCartierDivisor f p hp) := by rw [ht, hpoint]

/-- Original finite diagonal pullback on the left point section is
the original point Cartier class. -/
theorem finiteDiagonalCycleClass_kunnethSectionLeft (n : ℕ) :
    finiteLevelCohomologyPullback ℓ (kunnethSectionLeft f f p hp) n 2
        (finiteGraphCycleClass f f (𝟙 X) (Category.id_comp f) ℓ hℓ n) =
      finiteEffectiveCartierCycleClass f ℓ hℓ n
        (sectionEffectiveCartierDivisor f p hp) :=
  finiteDiagonalCycleClass_pointSection f p hp ℓ hℓ
    (kunnethSectionLeft f f p hp) (kunnethSectionLeft_comp_structure f p hp)
    (diagonalIdeal_comap_kunnethSectionLeft f p hp) n

/-- The right point section gives the same actual finite point class. -/
theorem finiteDiagonalCycleClass_kunnethSectionRight (n : ℕ) :
    finiteLevelCohomologyPullback ℓ (kunnethSectionRight f f p hp) n 2
        (finiteGraphCycleClass f f (𝟙 X) (Category.id_comp f) ℓ hℓ n) =
      finiteEffectiveCartierCycleClass f ℓ hℓ n
        (sectionEffectiveCartierDivisor f p hp) :=
  finiteDiagonalCycleClass_pointSection f p hp ℓ hℓ
    (kunnethSectionRight f f p hp) (kunnethSectionRight_comp_structure f p hp)
    (diagonalIdeal_comap_kunnethSectionRight f p hp) n

/-- The original integral diagonal restricts to the actual point
class on the left section. -/
theorem integralDiagonalCycleClass_kunnethSectionLeft :
    ellAdicCohomologyPullback ℓ (kunnethSectionLeft f f p hp) 2
        (integralGraphCycleClass f f (𝟙 X) (Category.id_comp f) ℓ hℓ) =
      integralEffectiveCartierCycleClass f ℓ hℓ
        (sectionEffectiveCartierDivisor f p hp) := by
  apply ellAdicCohomology_ext X ℓ 2
  intro n
  rw [ellAdicProjection_pullback, integralGraphCycleClass_projection,
    integralEffectiveCartierCycleClass_projection]
  exact finiteDiagonalCycleClass_kunnethSectionLeft f p hp ℓ hℓ n

/-- The original integral diagonal has the same actual point
restriction on the right section. -/
theorem integralDiagonalCycleClass_kunnethSectionRight :
    ellAdicCohomologyPullback ℓ (kunnethSectionRight f f p hp) 2
        (integralGraphCycleClass f f (𝟙 X) (Category.id_comp f) ℓ hℓ) =
      integralEffectiveCartierCycleClass f ℓ hℓ
        (sectionEffectiveCartierDivisor f p hp) := by
  apply ellAdicCohomology_ext X ℓ 2
  intro n
  rw [ellAdicProjection_pullback, integralGraphCycleClass_projection,
    integralEffectiveCartierCycleClass_projection]
  exact finiteDiagonalCycleClass_kunnethSectionRight f p hp ℓ hℓ n

/-- Actual rational scalar extension retains the original diagonal
restriction formula on the left section. -/
theorem rationalDiagonalCycleClass_kunnethSectionLeft :
    rationalEllAdicCohomologyPullback ℓ (kunnethSectionLeft f f p hp) 2
        (rationalGraphCycleClass f f (𝟙 X) (Category.id_comp f) ℓ hℓ) =
      rationalEffectiveCartierCycleClass f ℓ hℓ
        (sectionEffectiveCartierDivisor f p hp) := by
  change rationalEllAdicCohomologyPullback ℓ (kunnethSectionLeft f f p hp) 2
      ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]]
        integralGraphCycleClass f f (𝟙 X) (Category.id_comp f) ℓ hℓ) =
    (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] integralEffectiveCartierCycleClass f ℓ hℓ
      (sectionEffectiveCartierDivisor f p hp)
  rw [rationalEllAdicCohomologyPullback_tmul,
    integralDiagonalCycleClass_kunnethSectionLeft f p hp ℓ hℓ]

/-- The right section likewise recovers the original rational point
class from the actual diagonal. -/
theorem rationalDiagonalCycleClass_kunnethSectionRight :
    rationalEllAdicCohomologyPullback ℓ (kunnethSectionRight f f p hp) 2
        (rationalGraphCycleClass f f (𝟙 X) (Category.id_comp f) ℓ hℓ) =
      rationalEffectiveCartierCycleClass f ℓ hℓ
        (sectionEffectiveCartierDivisor f p hp) := by
  change rationalEllAdicCohomologyPullback ℓ (kunnethSectionRight f f p hp) 2
      ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]]
        integralGraphCycleClass f f (𝟙 X) (Category.id_comp f) ℓ hℓ) =
    (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] integralEffectiveCartierCycleClass f ℓ hℓ
      (sectionEffectiveCartierDivisor f p hp)
  rw [rationalEllAdicCohomologyPullback_tmul,
    integralDiagonalCycleClass_kunnethSectionRight f p hp ℓ hℓ]

end EtaleCohomology
