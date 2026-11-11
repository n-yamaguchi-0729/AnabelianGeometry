/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.CartierAdicCycleClass
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.DiagonalDivisorBundle
public import Nyll.EtaleCohomology.Classical.DiagonalSignedCycleSections
public import Nyll.EtaleCohomology.Classical.ExternalCupPullbackComposition
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.FiniteLevelCupPullback
public import Nyll.EtaleCohomology.Classical.GraphCartierCycleClass
public import Nyll.EtaleCohomology.Classical.RationalKunnethSections
public import Nyll.EtaleCohomology.Classical.SeparablyClosedAdic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Section normalization in the original finite coefficient groups

The actual Kummer comparison transports the signed diagonal calculation
to its original finite cyclic class. The actual cup pullback likewise
kills an external product with positive first degree, since its first
factor restricts through the algebraically closed point. These are the
two terms of the diagonal residual, on the same original section.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology.Classical

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
  (ℓ : ℕ) [Fact ℓ.Prime]

/-- Restricting an original finite external cup to the right point
section kills its positive-degree first factor. -/
theorem finiteLevelCup_kunnethSectionRight_eq_zero
    (n i j k : ℕ) (h : (i + 1) + j = k)
    (x : finiteLevelCohomology X ℓ n (i + 1))
    (y : finiteLevelCohomology Y ℓ n j) :
    finiteLevelCohomologyPullback ℓ (kunnethSectionRight f g p hp) n k
        (finiteLevelCup (pullback f g) ℓ n (i + 1) j k h
          (finiteLevelCohomologyPullback ℓ (pullback.fst f g) n (i + 1) x)
          (finiteLevelCohomologyPullback ℓ (pullback.snd f g) n j y)) = 0 := by
  have hfirst :
      finiteLevelCohomologyPullback ℓ (kunnethSectionRight f g p hp) n (i + 1)
          (finiteLevelCohomologyPullback ℓ (pullback.fst f g) n (i + 1) x) = 0 := by
    calc
      _ = finiteLevelCohomologyPullback ℓ
          (kunnethSectionRight f g p hp ≫ pullback.fst f g) n (i + 1) x :=
        (LinearMap.congr_fun (finiteLevelCohomologyPullback_comp
          (kunnethSectionRight f g p hp) (pullback.fst f g) ℓ n (i + 1)) x).symm
      _ = 0 := by
        rw [kunnethSectionRight_fst f g p hp,
          finiteLevelCohomologyPullback_comp g p ℓ n (i + 1), LinearMap.comp_apply,
          finiteLevelCohomology_eq_zero_of_isSepClosed K ℓ n i
            (finiteLevelCohomologyPullback ℓ p n (i + 1) x), map_zero]
  rw [finiteLevelCohomologyPullback_cup, hfirst, map_zero, AddMonoidHom.zero_apply]

end EtaleCohomology.Classical

namespace EtaleCohomology

open EtaleCohomology.Classical

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (.of K)) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  [IsIntegral (pullback f f)]
  (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The original finite signed diagonal, in the original coherent
cyclic coordinates, vanishes on its actual rigidifying section. -/
theorem finiteDiagonalSignedCycleClass_kunnethSectionRight (n : ℕ) :
    finiteLevelCohomologyPullback ℓ (kunnethSectionRight f f p hp) n 2
        (finiteEffectiveCartierCycleClass (pullback.snd f f ≫ f) ℓ hℓ n
            (graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)) -
          finiteEffectiveCartierCycleClass (pullback.snd f f ≫ f) ℓ hℓ n
            (diagonalEdgeEffectiveCartierDivisor f p hp)) = 0 := by
  apply (finiteLevelKummerCohomologyEquiv
    (kunnethSectionRight f f p hp ≫ (pullback.snd f f ≫ f)) ℓ hℓ n 2).injective
  rw [map_zero, finiteLevelKummerCohomologyEquiv_pullback, map_sub,
    finiteEffectiveCartierCycleClass_kummer, finiteEffectiveCartierCycleClass_kummer]
  exact diagonalSignedCycleClass_kunnethSectionRight f p hp
    (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
    (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)) _

end EtaleCohomology
