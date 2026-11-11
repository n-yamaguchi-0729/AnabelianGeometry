/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Nyll.EtaleCohomology.Sites.PullbackStalks
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Exact inverse image of set-valued étale sheaves

The stalk of the actual inverse image is the stalk at the composite geometric
point. Since geometric stalks are conservative, inverse image preserves finite
limits, including the fiber squares defining extension torsors.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)

local instance : RepresentablyFlat (etaleBaseChange f) :=
  flat_of_preservesFiniteLimits _

/-- Set-valued fibers at the comapped point and the composite point agree. -/
def geometricComapSetSheafFiberIso :
    ((Scheme.pointSmallEtale s).comap (etaleBaseChange f)
      (etaleBaseChange_coverPreserving f)).sheafFiber (A := Type u) ≅
      (Scheme.pointSmallEtale (s ≫ f)).sheafFiber :=
  geometricComapSheafFiberIsoOfCoefficients f s (Type u)

/-- The geometric stalk formula for the actual set-valued inverse image. -/
def etaleSetPullbackStalkIso :
    etaleSetPullback f ⋙ (Scheme.pointSmallEtale s).sheafFiber ≅
      (Scheme.pointSmallEtale (s ≫ f)).sheafFiber :=
  ((conjugateIsoEquiv
    ((etaleSetPullbackPushforwardAdjunction f).comp
      (Scheme.pointSmallEtale s).skyscraperSheafAdjunction)
    ((Scheme.pointSmallEtale s).comap (etaleBaseChange f)
      (etaleBaseChange_coverPreserving f)).skyscraperSheafAdjunction).symm
    ((Scheme.pointSmallEtale s).skyscraperSheafFunctorCompSheafPushforwardContinuous
      (etaleBaseChange f) (etaleBaseChange_coverPreserving f) (Type u))).symm ≪≫
    geometricComapSetSheafFiberIso f s

/-- Inverse image preserves finite limits, as detected on actual geometric stalks. -/
instance etaleSetPullback_preservesFiniteLimits :
    PreservesFiniteLimits (etaleSetPullback f) where
  preservesFiniteLimits J _ _ := by
    constructor
    intro K
    constructor
    intro c hc
    refine ⟨(Scheme.isConservativeFamilyOfPoints_pointSmallEtale'
      X).jointlyReflectIsomorphisms_type.jointlyReflectsLimit ?_⟩
    intro Φ
    apply Classical.choice
    rcases Φ with ⟨_, ⟨x⟩⟩
    let sx : Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
      (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm
        ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
    have : PreservesFiniteLimits
        (etaleSetPullback f ⋙ (Scheme.pointSmallEtale sx).sheafFiber) :=
      preservesFiniteLimits_of_natIso (etaleSetPullbackStalkIso f sx).symm
    exact ⟨isLimitOfPreserves
      (etaleSetPullback f ⋙ (Scheme.pointSmallEtale sx).sheafFiber) hc⟩

end EtaleCohomology
