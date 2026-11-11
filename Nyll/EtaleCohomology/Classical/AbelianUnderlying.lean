/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Sites.ModuleSetComparison
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Mathlib.CategoryTheory.Whiskering

/-!
# Underlying sets of actual abelian inverse images

Transport the proved module/set inverse-image comparison through the actual
integer-module equivalence defining abelian inverse image. The comparison
retains the original abelian sheaves and the existing set inverse image.
This allows their extension fibers to be compared as sheaves of sets.
-/

@[expose] public section

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor

namespace EtaleCohomology

/-- Forget the abelian group structure of an etale sheaf. -/
def etaleAbelianUnderlying (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology (Type u) :=
  sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})

/-- The underlying Type sheaf of an actual constant abelian sheaf is the
existing Type-valued constant sheaf on the same étale site. -/
def etaleConstantAbelianUnderlyingIso (X : Scheme.{u}) :
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
        etaleAbelianUnderlying X ≅
      forget AddCommGrpCat.{u} ⋙ constantSheaf X.smallEtaleTopology (Type u) := by
  let : X.smallEtaleTopology.PreservesSheafification (forget AddCommGrpCat.{u}) :=
    GrothendieckTopology.PreservesSheafification.transport
      X.smallEtaleTopology (Scheme.AffineEtale.topology X) (Scheme.AffineEtale.Spec X)
      (Type u) (forget AddCommGrpCat.{u})
  exact constantCommuteCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})

/-- The constant-sheaf comparison respects the sheafification unit, before
evaluation at any étale object. -/
theorem constantAbelianForgetToSheafify {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify J (Type w)]
    (U : AddCommGrpCat.{w} ⥤ Type w) [J.PreservesSheafification U]
    [J.HasSheafCompose U] (A : AddCommGrpCat.{w}) :
    whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj A)) U ≫
      (sheafifyComposeIso J U ((Functor.const Cᵒᵖ).obj A)).inv ≫
      sheafifyMap J (Functor.constComp Cᵒᵖ A U).hom =
    (Functor.constComp Cᵒᵖ A U).hom ≫
      toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj A)) := by
  calc
    _ = toSheafify J ((Functor.const Cᵒᵖ).obj A ⋙ U) ≫
        sheafifyMap J (Functor.constComp Cᵒᵖ A U).hom := by
      rw [← Category.assoc, CategoryTheory.sheafComposeIso_inv_fac]
    _ = (Functor.constComp Cᵒᵖ A U).hom ≫
        toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj A)) :=
      (CategoryTheory.toSheafify_naturality J (Functor.constComp Cᵒᵖ A U).hom).symm

theorem constantPresheafAdj_unit_app_eq_id {C : Type u} [Category.{v} C]
    {D : Type w} [Category.{v} D] (T : C) (hT : Limits.IsTerminal T) (A : D) :
    (constantPresheafAdj D hT).unit.app A = 𝟙 A := by
  change (Functor.constCompEvaluationObj D (Opposite.op T)).hom.app A = 𝟙 A
  rfl

/-- The integer-module equivalence preserves the original underlying sheaf of sets. -/
def integerSheafEquivalenceUnderlyingIso (X : Scheme.{u}) :
    (Classical.integerSheafEquivalence X.smallEtaleTopology).functor ⋙
      etaleAbelianUnderlying X ≅ etaleModuleUnderlying X (ULift.{u} ℤ) :=
  Iso.refl _

/-- The inverse integer-module equivalence preserves the original underlying sheaf of sets. -/
def integerSheafInverseUnderlyingIso (X : Scheme.{u}) :
    (Classical.integerSheafEquivalence X.smallEtaleTopology).inverse ⋙
      etaleModuleUnderlying X (ULift.{u} ℤ) ≅ etaleAbelianUnderlying X :=
  Functor.isoWhiskerLeft (Classical.integerSheafEquivalence X.smallEtaleTopology).inverse
      (integerSheafEquivalenceUnderlyingIso X).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Classical.integerSheafEquivalence X.smallEtaleTopology).counitIso
      (etaleAbelianUnderlying X) ≪≫ Functor.leftUnitor _

/-- The actual abelian inverse image commutes with forgetting to sheaves of sets. -/
def etaleAbelianPullbackUnderlyingIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleAbelianPullback f ⋙ etaleAbelianUnderlying X ≅
      etaleAbelianUnderlying Y ⋙ etaleSetPullback f :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Classical.integerSheafEquivalence Y.smallEtaleTopology).inverse
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (etalePullback f (ULift.{u} ℤ))
          (integerSheafEquivalenceUnderlyingIso X)) ≪≫
    Functor.isoWhiskerLeft (Classical.integerSheafEquivalence Y.smallEtaleTopology).inverse
      (etalePullbackModuleUnderlyingIso f (ULift.{u} ℤ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (integerSheafInverseUnderlyingIso Y) (etaleSetPullback f)

end EtaleCohomology
