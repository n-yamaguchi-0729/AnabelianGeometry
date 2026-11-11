/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Composition of étale inverse and direct image

The pullback pasting isomorphism on the small étale sites gives the direct
image composition isomorphism. The corresponding inverse image comparison
follows from the constructed adjunctions and uniqueness of left adjoints.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (R : Type u) [CommRing R]

/-- Iterated direct image is direct image along the composite morphism. -/
def etalePushforwardCompIso :
    etalePushforward f R ⋙ etalePushforward g R ≅ etalePushforward (f ≫ g) R := by
  let e : etaleBaseChange (f ≫ g) ≅ etaleBaseChange g ⋙ etaleBaseChange f :=
    MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme from @Etale) (Q := ⊤) f g
  exact Functor.sheafPushforwardContinuousComp' e.symm
    (ModuleCat.{u} R) Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology

/-- Inverse image along a composite is the iterated inverse image. -/
def etalePullbackCompIso :
    etalePullback (f ≫ g) R ≅ etalePullback g R ⋙ etalePullback f R :=
  (etalePullbackPushforwardAdjunction (f ≫ g) R).leftAdjointUniq
    (((etalePullbackPushforwardAdjunction g R).comp
      (etalePullbackPushforwardAdjunction f R)).ofNatIsoRight (etalePushforwardCompIso f g R))

end EtaleCohomology
