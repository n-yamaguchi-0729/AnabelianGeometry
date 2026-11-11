/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.HomInvertibleKerCompEqId
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.EffectiveCartierIdeal
public import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivOfPoint
public import Nyll.EtaleCohomology.Classical.RationalKunnethSections
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Actual diagonal ideals on the two point sections

Pulling the original diagonal back along either original point section
gives the original point kernel. The proof constructs both Cartesian
squares from their universal property. For a separated smooth relative
curve that point kernel is an actual effective Cartier divisor.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology.Classical

variable {X S : Scheme.{u}} (f : X ⟶ S) (p : S ⟶ X) (hp : p ≫ f = 𝟙 S)

/-- The actual left point section preserves the original structure map. -/
theorem kunnethSectionLeft_comp_structure :
    kunnethSectionLeft f f p hp ≫ (pullback.snd f f ≫ f) = f := by
  rw [← Category.assoc, kunnethSectionLeft_snd, Category.assoc, hp,
    Category.comp_id]

/-- The actual right point section preserves that same structure map. -/
theorem kunnethSectionRight_comp_structure :
    kunnethSectionRight f f p hp ≫ (pullback.snd f f ≫ f) = f := by
  rw [← Category.assoc, kunnethSectionRight_snd, Category.id_comp]

/-- The original left point section meets the original diagonal in the
original point, as an actual Cartesian square. -/
theorem diagonal_kunnethSectionLeft_isPullback :
    IsPullback p p (kunnethSectionLeft f f p hp)
      (graphOver f (𝟙 X) (Category.id_comp f)) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · apply pullback.hom_ext
    · simp only [Category.assoc, kunnethSectionLeft_fst, graphOver_fst,
        Category.comp_id]
    · simp only [Category.assoc, kunnethSectionLeft_snd, graphOver_snd,
        Category.comp_id]
      rw [← Category.assoc, hp, Category.id_comp]
  · intro T a b h₁ h₂
    have h := congrArg (fun k : T ⟶ X => k ≫ f) h₁
    simpa only [Category.assoc, hp, Category.comp_id] using h
  · intro T a b h
    have hab : a = b := by
      have h' := congrArg (fun k : T ⟶ pullback f f => k ≫ pullback.fst f f) h
      simpa only [Category.assoc, kunnethSectionLeft_fst, graphOver_fst,
        Category.comp_id] using h'
    have hfp : a ≫ f ≫ p = b := by
      have h' := congrArg (fun k : T ⟶ pullback f f => k ≫ pullback.snd f f) h
      simpa only [Category.assoc, kunnethSectionLeft_snd, graphOver_snd,
        Category.comp_id] using h'
    exact ⟨a ≫ f, (Category.assoc a f p).trans (hfp.trans hab.symm),
      (Category.assoc a f p).trans hfp⟩

/-- The original right point section has the same actual diagonal
intersection, with the two projection equations interchanged. -/
theorem diagonal_kunnethSectionRight_isPullback :
    IsPullback p p (kunnethSectionRight f f p hp)
      (graphOver f (𝟙 X) (Category.id_comp f)) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · apply pullback.hom_ext
    · simp only [Category.assoc, kunnethSectionRight_fst, graphOver_fst,
        Category.comp_id]
      rw [← Category.assoc, hp, Category.id_comp]
    · simp only [Category.assoc, kunnethSectionRight_snd, graphOver_snd,
        Category.comp_id]
  · intro T a b h₁ h₂
    have h := congrArg (fun k : T ⟶ X => k ≫ f) h₁
    simpa only [Category.assoc, hp, Category.comp_id] using h
  · intro T a b h
    have hab : a = b := by
      have h' := congrArg (fun k : T ⟶ pullback f f => k ≫ pullback.snd f f) h
      simpa only [Category.assoc, kunnethSectionRight_snd, graphOver_snd,
        Category.comp_id] using h'
    have hfp : a ≫ f ≫ p = b := by
      have h' := congrArg (fun k : T ⟶ pullback f f => k ≫ pullback.fst f f) h
      simpa only [Category.assoc, kunnethSectionRight_fst, graphOver_fst,
        Category.comp_id] using h'
    exact ⟨a ≫ f, (Category.assoc a f p).trans (hfp.trans hab.symm),
      (Category.assoc a f p).trans hfp⟩

variable [IsSeparated f]

/-- The full original diagonal ideal pulls back to the full point
kernel along the left point section. -/
theorem diagonalIdeal_comap_kunnethSectionLeft :
    (graphOver f (𝟙 X) (Category.id_comp f)).ker.comap
        (kunnethSectionLeft f f p hp) = p.ker := by
  let H := diagonal_kunnethSectionLeft_isPullback f p hp
  exact (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
    (graphOver f (𝟙 X) (Category.id_comp f))
    (kunnethSectionLeft f f p hp)).symm.trans
      ((Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom
        (pullback.fst (kunnethSectionLeft f f p hp)
          (graphOver f (𝟙 X) (Category.id_comp f)))).symm.trans
            (congrArg (fun q : S ⟶ X => q.ker) H.isoPullback_hom_fst))

/-- The same ideal equality for the right point section. -/
theorem diagonalIdeal_comap_kunnethSectionRight :
    (graphOver f (𝟙 X) (Category.id_comp f)).ker.comap
        (kunnethSectionRight f f p hp) = p.ker := by
  let H := diagonal_kunnethSectionRight_isPullback f p hp
  exact (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
    (graphOver f (𝟙 X) (Category.id_comp f))
    (kunnethSectionRight f f p hp)).symm.trans
      ((Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom
        (pullback.fst (kunnethSectionRight f f p hp)
          (graphOver f (𝟙 X) (Category.id_comp f)))).symm.trans
            (congrArg (fun q : S ⟶ X => q.ker) H.isoPullback_hom_fst))

end EtaleCohomology.Classical

namespace EtaleCohomology

/-- The original kernel of a section of a separated smooth relative
curve, with the genuine Cartier regularity supplied by that section. -/
def sectionEffectiveCartierDivisor
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] (p : S ⟶ X) (hp : p ≫ f = 𝟙 S) :
    Scheme.EffectiveCartierDivisor X :=
  ⟨p.ker, (Scheme.Hom.isInvertible_ker_of_comp_eq_id p hp).isEffectiveCartier⟩

/-- The divisor retains the actual point kernel ideal. -/
theorem sectionEffectiveCartierDivisor_ideal
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] (p : S ⟶ X) (hp : p ≫ f = 𝟙 S) :
    (sectionEffectiveCartierDivisor f p hp).1 = p.ker := rfl

end EtaleCohomology
