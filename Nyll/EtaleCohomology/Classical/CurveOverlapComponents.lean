/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.EtaleCohomology.Classical.EtaleObjectComponentDecomposition
public import Nyll.EtaleCohomology.Sites.GaloisSections
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Actual integral components of a finite étale curve overlap

The original self-overlap of a finite étale curve cover is finite over
the curve. Smoothness supplies domain stalks, and properness supplies
Noetherianity. Its actual reduced components therefore give integral
finite étale objects, with the same original two projection maps. These
are the very components used by cohomology detection and by the original
division-transition calculations.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace EtaleCohomology

variable {C : Scheme.{u}} (B : FiniteEtale C)

/-- The original categorical overlap of the canonical parameter cover. -/
abbrev finiteEtaleCoverOverlap : C.Etale :=
  pullback (finiteEtaleCoverBaseMap C B) (finiteEtaleCoverBaseMap C B)

instance finiteEtaleCoverOverlap_finite : IsFinite (finiteEtaleCoverOverlap B).hom := by
  have : IsFinite ((finiteEtaleInclusion C).obj B).hom :=
    (inferInstance : IsFinite B.hom)
  exact etaleTerminalPullback_finite C
    (MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) C)
    (finiteEtaleCoverBaseMap C B) (finiteEtaleCoverBaseMap C B)

section Curve

variable {K : Type u} [Field K] (c : C ⟶ Spec (.of K)) [Smooth c] [IsProper c]

omit [Smooth c] in
include c in
/-- Properness of the actual finite parameter overlap makes its
actual reduced-component index finite. -/
theorem curveEtaleCoverOverlap_isNoetherian :
    IsNoetherian (finiteEtaleCoverOverlap B).left :=
  smoothProperScheme_isNoetherian ((finiteEtaleCoverOverlap B).hom ≫ c)

omit [IsProper c] in
include c in
/-- The actual overlap is smooth over the field, so all its original
stalks are domains. -/
theorem curveEtaleCoverOverlap_stalk_isDomain :
    ∀ z : (finiteEtaleCoverOverlap B).left,
      IsDomain ((finiteEtaleCoverOverlap B).left.presheaf.stalk z) :=
  smoothSchemeDomainStalks ((finiteEtaleCoverOverlap B).hom ≫ c)

end Curve

section Components

variable [IsNoetherian (finiteEtaleCoverOverlap B).left]
  (hdom : ∀ z : (finiteEtaleCoverOverlap B).left,
    IsDomain ((finiteEtaleCoverOverlap B).left.presheaf.stalk z))
  (Z : irreducibleComponents (finiteEtaleCoverOverlap B).left)

/-- The same original reduced overlap component as a finite étale
object over the unchanged curve. -/
def finiteEtaleCoverOverlapComponent : FiniteEtale C := by
  let U : C.Etale := etaleObjectReducedComponent (finiteEtaleCoverOverlap B) hdom Z
  have : IsFiniteEtale U.hom := { toIsFinite := inferInstance, toEtale := inferInstance }
  exact FiniteEtale.mk U.hom

instance finiteEtaleCoverOverlapComponent_integral :
    IsIntegral (finiteEtaleCoverOverlapComponent B hdom Z).left :=
  etaleObjectReducedComponent_integral (finiteEtaleCoverOverlap B) hdom Z

/-- Forgetting finiteness retains the original component object used
by the original cohomology detection theorem. -/
theorem finiteEtaleCoverOverlapComponent_inclusion :
    (finiteEtaleInclusion C).obj (finiteEtaleCoverOverlapComponent B hdom Z) =
      etaleObjectReducedComponent (finiteEtaleCoverOverlap B) hdom Z := rfl

/-- The first original overlap projection of the actual component. -/
def finiteEtaleCoverOverlapComponentFirst :
    finiteEtaleCoverOverlapComponent B hdom Z ⟶ B :=
  MorphismProperty.Over.homMk
    (etaleObjectReducedComponentMap (finiteEtaleCoverOverlap B) hdom Z ≫
      pullback.fst (finiteEtaleCoverBaseMap C B) (finiteEtaleCoverBaseMap C B)).left
    (etaleObjectReducedComponentMap (finiteEtaleCoverOverlap B) hdom Z ≫
      pullback.fst (finiteEtaleCoverBaseMap C B) (finiteEtaleCoverBaseMap C B)).w

/-- The second original overlap projection of the same component. -/
def finiteEtaleCoverOverlapComponentSecond :
    finiteEtaleCoverOverlapComponent B hdom Z ⟶ B :=
  MorphismProperty.Over.homMk
    (etaleObjectReducedComponentMap (finiteEtaleCoverOverlap B) hdom Z ≫
      pullback.snd (finiteEtaleCoverBaseMap C B) (finiteEtaleCoverBaseMap C B)).left
    (etaleObjectReducedComponentMap (finiteEtaleCoverOverlap B) hdom Z ≫
      pullback.snd (finiteEtaleCoverBaseMap C B) (finiteEtaleCoverBaseMap C B)).w

/-- The first map is exactly the original component inclusion followed
by the first projection, in the same original small étale site. -/
theorem finiteEtaleCoverOverlapComponentFirst_inclusion :
    (finiteEtaleInclusion C).map (finiteEtaleCoverOverlapComponentFirst B hdom Z) =
      etaleObjectReducedComponentMap (finiteEtaleCoverOverlap B) hdom Z ≫
        pullback.fst (finiteEtaleCoverBaseMap C B) (finiteEtaleCoverBaseMap C B) := rfl

/-- The second map retains exactly the second original projection. -/
theorem finiteEtaleCoverOverlapComponentSecond_inclusion :
    (finiteEtaleInclusion C).map (finiteEtaleCoverOverlapComponentSecond B hdom Z) =
      etaleObjectReducedComponentMap (finiteEtaleCoverOverlap B) hdom Z ≫
        pullback.snd (finiteEtaleCoverBaseMap C B) (finiteEtaleCoverBaseMap C B) := rfl

end Components

end EtaleCohomology
