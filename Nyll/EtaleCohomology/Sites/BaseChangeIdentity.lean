/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.BaseChange
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-! # The actual identity base change on the small étale site -/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable (X : Scheme.{u})

/-- Pullback along the identity recovers the original étale object. -/
def etaleBaseChangeIdObjIso (U : X.Etale) :
    (etaleBaseChange (𝟙 X)).obj U ≅ U := by
  let e : pullback U.hom (𝟙 X) ≅ U.left := asIso (pullback.fst U.hom (𝟙 X))
  exact MorphismProperty.Over.isoMk e (by
    change pullback.fst U.hom (𝟙 X) ≫ U.hom = pullback.snd U.hom (𝟙 X)
    rw [pullback.condition, Category.comp_id])

/-- The comparison with the identity site functor uses the actual first
projection of pullback by the identity scheme morphism. -/
def etaleBaseChangeIdIso : etaleBaseChange (𝟙 X) ≅ 𝟭 X.Etale :=
  NatIso.ofComponents (etaleBaseChangeIdObjIso X) (by
    intro U V h
    let m : pullback U.hom (𝟙 X) ⟶ pullback V.hom (𝟙 X) :=
      ((etaleBaseChange (𝟙 X)).map h).left
    have hm : m ≫ pullback.fst V.hom (𝟙 X) = pullback.fst U.hom (𝟙 X) ≫ h.left :=
      pullback.lift_fst _ _ _
    apply MorphismProperty.Over.Hom.ext
    change m ≫ pullback.fst V.hom (𝟙 X) = pullback.fst U.hom (𝟙 X) ≫ h.left
    exact hm)

end EtaleCohomology
