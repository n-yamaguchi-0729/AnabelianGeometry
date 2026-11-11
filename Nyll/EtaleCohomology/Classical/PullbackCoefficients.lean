/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.CoefficientSheaves
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Forgetting coefficients under actual étale inverse image

The right adjoint of forgetting coefficients acts pointwise on sheaves and
commutes with direct image. Uniqueness of left adjoints therefore identifies
module inverse image followed by forgetting with abelian inverse image.
The pointwise coefficient adjunction also proves compatibility with the
actual inverse-image/direct-image units.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor

namespace EtaleCohomology

/-- The right adjoint to forgetting a module coefficient action. -/
abbrev coefficientRightAdjoint (R : Type u) [CommRing R] :
    AddCommGrpCat.{u} ⥤ ModuleCat.{u} R :=
  (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).rightAdjoint

/-- The coefficient right adjoint applied pointwise to étale sheaves. -/
def coefficientSheafRightAdjoint (X : Scheme.{u}) (R : Type u) [CommRing R] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
  sheafCompose X.smallEtaleTopology (coefficientRightAdjoint R)

/-- Forgetting coefficients is left adjoint to the pointwise coefficient right adjoint. -/
def coefficientSheafAdjunction (X : Scheme.{u}) (R : Type u) [CommRing R] :
    Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R) ⊣
      coefficientSheafRightAdjoint X R := by
  let adj := Adjunction.ofIsLeftAdjoint
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  exact
    { unit :=
        { app := fun F => ObjectProperty.homMk (whiskerLeft F.obj adj.unit)
          naturality := fun F G φ => by
            apply Sheaf.hom_ext
            apply NatTrans.ext
            funext U
            exact adj.unit.naturality (φ.hom.app U) }
      counit :=
        { app := fun F => ObjectProperty.homMk (whiskerLeft F.obj adj.counit)
          naturality := fun F G φ => by
            apply Sheaf.hom_ext
            apply NatTrans.ext
            funext U
            exact adj.counit.naturality (φ.hom.app U) }
      left_triangle_components := fun F => by
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext U
        exact adj.left_triangle_components (F.obj.obj U)
      right_triangle_components := fun F => by
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext U
        exact adj.right_triangle_components (F.obj.obj U) }

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]

/-- Actual module inverse image commutes with forgetting the coefficient action. -/
def etalePullbackForgetCoefficientsIso :
    etalePullback f R ⋙
        Classical.forgetCoefficients.{u + 1, u, u, u} (J := X.smallEtaleTopology) ≅
      Classical.forgetCoefficients.{u + 1, u, u, u} (J := Y.smallEtaleTopology) ⋙
        etaleAbelianPullback f :=
  ((etalePullbackPushforwardAdjunction f R).comp
    (coefficientSheafAdjunction X R)).leftAdjointUniq
      ((coefficientSheafAdjunction Y R).comp
        (etaleAbelianPullbackPushforwardAdjunction f))

/-- The coefficient comparison carries the forgotten actual module unit to
the actual abelian unit. -/
theorem etalePullbackForgetCoefficientsIso_unit
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) :
    (Classical.forgetCoefficients.{u + 1, u, u, u} (J := Y.smallEtaleTopology)).map
        ((etalePullbackPushforwardAdjunction f R).unit.app F) ≫
      (etaleAbelianPushforward f).map
        ((etalePullbackForgetCoefficientsIso f R).hom.app F) =
    (etaleAbelianPullbackPushforwardAdjunction f).unit.app
      (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) := by
  let adjX := coefficientSheafAdjunction X R
  let adjY := coefficientSheafAdjunction Y R
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((etalePullbackPushforwardAdjunction f R).comp adjX)
    (adjY.comp (etaleAbelianPullbackPushforwardAdjunction f)) F
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  have hn :
      (etalePullbackPushforwardAdjunction f R).unit.app F ≫
          (etalePushforward f R).map (adjX.unit.app ((etalePullback f R).obj F)) =
        adjY.unit.app F ≫
          (coefficientSheafRightAdjoint Y R).map
            ((Classical.forgetCoefficients.{u + 1, u, u, u}
              (J := Y.smallEtaleTopology)).map
                ((etalePullbackPushforwardAdjunction f R).unit.app F)) :=
    adjY.unit.naturality ((etalePullbackPushforwardAdjunction f R).unit.app F)
  apply (adjY.homEquiv F _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  erw [Functor.map_comp]
  rw [← Category.assoc, ← hn]
  exact h

end EtaleCohomology
