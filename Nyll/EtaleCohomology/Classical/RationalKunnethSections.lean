/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ExternalCupPullbackComposition
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalExternalCupPullback
public import Nyll.EtaleCohomology.Classical.RationalKunnethMap
public import Nyll.EtaleCohomology.Classical.SeparablyClosedAdic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Actual point sections of the original Künneth map

A section of either factor defines the corresponding section of the
actual product projection. Original cohomological pullback along it
retracts that projection. Over a separably closed field the other
projection factors through the actual field point and vanishes in
positive degree. The same calculation kills actual external cup when
its restricted point factor has positive degree.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology.Classical

section SchemeSections

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- A section of the second factor gives the actual section of the
first product projection. -/
def kunnethSectionLeft (p : S ⟶ Y) (hp : p ≫ g = 𝟙 S) : X ⟶ pullback f g :=
  pullback.lift (𝟙 X) (f ≫ p) (by
    rw [Category.id_comp, Category.assoc, hp, Category.comp_id])

/-- A section of the first factor gives the actual section of the
second product projection. -/
def kunnethSectionRight (p : S ⟶ X) (hp : p ≫ f = 𝟙 S) : Y ⟶ pullback f g :=
  pullback.lift (g ≫ p) (𝟙 Y) (by
    rw [Category.assoc, hp, Category.comp_id, Category.id_comp])

theorem kunnethSectionLeft_fst (p : S ⟶ Y) (hp : p ≫ g = 𝟙 S) :
    kunnethSectionLeft f g p hp ≫ pullback.fst f g = 𝟙 X :=
  pullback.lift_fst _ _ _

theorem kunnethSectionLeft_snd (p : S ⟶ Y) (hp : p ≫ g = 𝟙 S) :
    kunnethSectionLeft f g p hp ≫ pullback.snd f g = f ≫ p :=
  pullback.lift_snd _ _ _

theorem kunnethSectionRight_fst (p : S ⟶ X) (hp : p ≫ f = 𝟙 S) :
    kunnethSectionRight f g p hp ≫ pullback.fst f g = g ≫ p :=
  pullback.lift_fst _ _ _

theorem kunnethSectionRight_snd (p : S ⟶ X) (hp : p ≫ f = 𝟙 S) :
    kunnethSectionRight f g p hp ≫ pullback.snd f g = 𝟙 Y :=
  pullback.lift_snd _ _ _

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The original first projection pullback has the actual point-section
pullback as a left inverse, in every degree. -/
theorem rationalEllAdicPullback_kunnethSectionLeft_fst
    (p : S ⟶ Y) (hp : p ≫ g = 𝟙 S) (i : ℕ) :
    (rationalEllAdicCohomologyPullback ℓ (kunnethSectionLeft f g p hp) i).comp
        (rationalEllAdicCohomologyPullback ℓ (pullback.fst f g) i) = 1 := by
  rw [← rationalEllAdicCohomologyPullback_comp, kunnethSectionLeft_fst,
    rationalEllAdicCohomologyPullback_id]

/-- The original second projection pullback has the corresponding
actual point-section pullback as a left inverse. -/
theorem rationalEllAdicPullback_kunnethSectionRight_snd
    (p : S ⟶ X) (hp : p ≫ f = 𝟙 S) (i : ℕ) :
    (rationalEllAdicCohomologyPullback ℓ (kunnethSectionRight f g p hp) i).comp
        (rationalEllAdicCohomologyPullback ℓ (pullback.snd f g) i) = 1 := by
  rw [← rationalEllAdicCohomologyPullback_comp, kunnethSectionRight_snd,
    rationalEllAdicCohomologyPullback_id]

end SchemeSections

section SeparablyClosedBase

variable (K : Type u) [Field K] [IsSepClosed K] (ℓ : ℕ) [Fact ℓ.Prime]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
  (g : Y ⟶ Spec (CommRingCat.of K))

/-- On the actual left point section, the other original projection
pullback is zero in every positive degree. -/
theorem rationalEllAdicPullback_kunnethSectionLeft_snd
    (p : Spec (CommRingCat.of K) ⟶ Y) (hp : p ≫ g = 𝟙 _) (i : ℕ) :
    (rationalEllAdicCohomologyPullback ℓ (kunnethSectionLeft f g p hp) (i + 1)).comp
        (rationalEllAdicCohomologyPullback ℓ (pullback.snd f g) (i + 1)) = 0 := by
  rw [← rationalEllAdicCohomologyPullback_comp, kunnethSectionLeft_snd]
  exact rationalEllAdicCohomologyPullback_through_isSepClosed K ℓ f p i

/-- The other original projection likewise vanishes on the actual
right point section in positive degree. -/
theorem rationalEllAdicPullback_kunnethSectionRight_fst
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) (i : ℕ) :
    (rationalEllAdicCohomologyPullback ℓ (kunnethSectionRight f g p hp) (i + 1)).comp
        (rationalEllAdicCohomologyPullback ℓ (pullback.fst f g) (i + 1)) = 0 := by
  rw [← rationalEllAdicCohomologyPullback_comp, kunnethSectionRight_fst]
  exact rationalEllAdicCohomologyPullback_through_isSepClosed K ℓ g p i

/-- Restriction to the actual left point section kills external cup
whenever the original second factor has positive degree. -/
theorem rationalEllAdicExternalCup_kunnethSectionLeft_eq_zero
    (p : Spec (CommRingCat.of K) ⟶ Y) (hp : p ≫ g = 𝟙 _)
    (i j n : ℕ) (h : i + (j + 1) = n)
    (x : rationalEllAdicCohomology ℓ X i) (y : rationalEllAdicCohomology ℓ Y (j + 1)) :
    rationalEllAdicCohomologyPullback ℓ (kunnethSectionLeft f g p hp) n
        (rationalEllAdicExternalCup ℓ f g i (j + 1) n h x y) = 0 := by
  rw [rationalEllAdicExternalCup_pullback, kunnethSectionLeft_fst,
    kunnethSectionLeft_snd, rationalEllAdicCohomologyPullback_id, Module.End.one_apply,
    rationalEllAdicCohomologyPullback_through_isSepClosed K ℓ f p j,
    LinearMap.zero_apply, map_zero]

/-- Restriction to the actual right point section kills external cup
whenever the original first factor has positive degree. -/
theorem rationalEllAdicExternalCup_kunnethSectionRight_eq_zero
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (i j n : ℕ) (h : (i + 1) + j = n)
    (x : rationalEllAdicCohomology ℓ X (i + 1)) (y : rationalEllAdicCohomology ℓ Y j) :
    rationalEllAdicCohomologyPullback ℓ (kunnethSectionRight f g p hp) n
        (rationalEllAdicExternalCup ℓ f g (i + 1) j n h x y) = 0 := by
  rw [rationalEllAdicExternalCup_pullback, kunnethSectionRight_fst,
    kunnethSectionRight_snd, rationalEllAdicCohomologyPullback_id, Module.End.one_apply,
    rationalEllAdicCohomologyPullback_through_isSepClosed K ℓ g p i,
    LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

end SeparablyClosedBase

end EtaleCohomology.Classical
