/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CartierCycleAdditivity
public import Nyll.EtaleCohomology.Classical.CartierCyclePullback
public import Nyll.EtaleCohomology.Classical.DiagonalDivisorBundle
public import Nyll.EtaleCohomology.Classical.DiagonalPointSectionIdeals
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.GraphCartierCycleClass
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.RationalKunnethSections
public import Nyll.EtaleCohomology.Classical.RootsOfUnityPullbackComposition
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The original signed diagonal vanishes on its rigidifying section

The diagonal meets the section in the actual point divisor. Of the two
point pullbacks, the first restricts through the algebraically closed
base and the second restricts to the point divisor itself. Thus the
original diagonal-minus-edge Cartier class is zero on that section,
in the original Kummer cohomology for every invertible exponent.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open EtaleCohomology.Classical

namespace EtaleCohomology

section WithoutAlgebraicClosure

variable {K : Type u} [Field K]
  {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (.of K)) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  [IsIntegral (pullback f f)]
  (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) {n : ℕ}

/-- The actual Cartesian intersection computes the original native
diagonal class on the right point section. -/
theorem diagonalCycleClass_kunnethSectionRight
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤)))
    (hnY : IsUnit (n : Γ(pullback f f, ⊤))) :
    etaleRootsOfUnityCohomologyPullback (kunnethSectionRight f f p hp) n 2
        (effectiveCartierCycleClass
          (graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)) hn hnY) =
      effectiveCartierCycleClass (sectionEffectiveCartierDivisor f p hp) hn hnX := by
  let D := graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)
  let σ := kunnethSectionRight f f p hp
  have hI : D.1.comap σ = p.ker := diagonalIdeal_comap_kunnethSectionRight f p hp
  have hD : (D.1.comap σ).IsEffectiveCartier := by
    rw [hI]
    exact (sectionEffectiveCartierDivisor f p hp).2
  have hpoint : (⟨D.1.comap σ, hD⟩ : Scheme.EffectiveCartierDivisor X) =
      sectionEffectiveCartierDivisor f p hp := Subtype.ext hI
  exact (effectiveCartierCycleClass_pullback σ D hD hn hnY hnX).trans
    (congrArg (fun E => effectiveCartierCycleClass E hn hnX) hpoint)

/-- The original product of the two point ideals has exactly the sum
of the original projection classes, before any coefficient comparison. -/
theorem diagonalEdgeEffectiveCartierDivisor_cycleClass
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤)))
    (hnY : IsUnit (n : Γ(pullback f f, ⊤))) :
    effectiveCartierCycleClass (diagonalEdgeEffectiveCartierDivisor f p hp) hn hnY =
      etaleRootsOfUnityCohomologyPullback (pullback.fst f f) n 2
          (effectiveCartierCycleClass (sectionEffectiveCartierDivisor f p hp) hn hnX) +
        etaleRootsOfUnityCohomologyPullback (pullback.snd f f) n 2
          (effectiveCartierCycleClass (sectionEffectiveCartierDivisor f p hp) hn hnX) := by
  let P := sectionEffectiveCartierDivisor f p hp
  let A := productPointFstEffectiveCartierDivisor f p hp
  let B := productPointSndEffectiveCartierDivisor f p hp
  change effectiveCartierCycleClass ⟨A.1 * B.1, A.2.mul B.2⟩ hn hnY = _
  rw [effectiveCartierCycleClass_mul,
    effectiveCartierCycleClass_pullback (pullback.fst f f) P A.2 hn hnX hnY,
    effectiveCartierCycleClass_pullback (pullback.snd f f) P B.2 hn hnX hnY]
  exact congrArg₂ (fun C D : Scheme.EffectiveCartierDivisor (pullback f f) =>
    effectiveCartierCycleClass C hn hnY + effectiveCartierCycleClass D hn hnY)
    (Subtype.ext (show A.1 = P.1.comap (pullback.fst f f) from rfl))
    (Subtype.ext (show B.1 = P.1.comap (pullback.snd f f) from rfl))

end WithoutAlgebraicClosure

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (.of K)) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  [IsIntegral (pullback f f)]
  (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) {n : ℕ}

/-- The original signed diagonal is normalized by the actual right
point section. No vanishing or comparison on the ambient surface is
assumed: only the positive cohomology of the base point is used. -/
theorem diagonalSignedCycleClass_kunnethSectionRight
    (hn : 0 < n) (hnK : IsUnit (n : K))
    (hnY : IsUnit (n : Γ(pullback f f, ⊤))) :
    etaleRootsOfUnityCohomologyPullback (kunnethSectionRight f f p hp) n 2
        (effectiveCartierCycleClass
            (graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)) hn hnY -
          effectiveCartierCycleClass (diagonalEdgeEffectiveCartierDivisor f p hp)
            hn hnY) = 0 := by
  let hnX := etaleKummerExponentUnit_of_base f hnK
  rw [map_sub, diagonalCycleClass_kunnethSectionRight f p hp hn hnX hnY,
    diagonalEdgeEffectiveCartierDivisor_cycleClass f p hp hn hnX hnY, map_add,
    ← etaleRootsOfUnityCohomologyPullback_comp
      (kunnethSectionRight f f p hp) (pullback.fst f f) f hn hnK,
    ← etaleRootsOfUnityCohomologyPullback_comp
      (kunnethSectionRight f f p hp) (pullback.snd f f) f hn hnK,
    kunnethSectionRight_fst, kunnethSectionRight_snd,
    etaleRootsOfUnityCohomologyPullback_through_field_eq_zero f p f hn hnK 1,
    etaleRootsOfUnityCohomologyPullback_id f hn hnK, zero_add, sub_self]

end EtaleCohomology
