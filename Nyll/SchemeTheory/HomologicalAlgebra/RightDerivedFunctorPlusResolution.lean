/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.FullSubcategory
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Actual injective resolutions compute the bounded below derived functor

For a given injective resolution, its actual augmentation is extended from
nonnegative to integer degrees. The resulting quasi-isomorphism, followed by
the native right-derived unit on the complex of injectives, constructs the
comparison in the derived category. No comparison is supplied as a premise.
-/

@[expose] public section

noncomputable section

universe uC vC wC uD vD wD

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- The actual derived unit is invertible on any bounded below complex
whose terms are injective, without requiring a chosen presentation of that
complex in the full subcategory of injective objects. -/
theorem rightDerivedFunctorPlusUnit_isIso_of_injective
    (K : CochainComplex.Plus C) [∀ n : ℤ, Injective (K.obj.X n)] :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  obtain ⟨n, hn⟩ := K.property
  let L' : CochainComplex (InjectiveObject C) ℤ :=
    HomologicalComplex.liftObjectProperty (isInjective C) K.obj inferInstance
  have hL' : L'.IsStrictlyGE n := by
    rw [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff
      L' (InjectiveObject.ι C)]
    exact hn
  let L : CochainComplex.Plus (InjectiveObject C) := ⟨L', n, hL'⟩
  let e : (InjectiveObject.ι C).mapCochainComplexPlus.obj L ≅ K :=
    ObjectProperty.isoMk _ (Iso.refl K.obj)
  exact (NatTrans.isIso_app_iff_of_iso F.rightDerivedFunctorPlusUnit e).mp
    inferInstance

end CategoryTheory.Functor

namespace CategoryTheory.InjectiveResolution

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  {A : C} (I : InjectiveResolution A)
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- A given actual injective resolution computes the native right-derived
functor on the degree-zero object. The target is the actual image of the
zero-extended resolution, in the unbounded derived category. -/
def rightDerivedFunctorPlusIso :
    DerivedCategory.Plus.ι.obj
      (F.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor C 0).obj A)) ≅
      DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (I.cocomplex.extend ComplexShape.embeddingUpNat)) := by
  let L : CochainComplex.Plus C :=
    ⟨I.cocomplex.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
  let S : CochainComplex.Plus C :=
    ⟨(CochainComplex.singleFunctor C 0).obj A, 0, inferInstance⟩
  let s : S ⟶ L := ObjectProperty.homMk
    ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat A 0 0 rfl).inv ≫
      HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat)
  have : QuasiIso s.hom := by
    change QuasiIso
      ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat A 0 0 rfl).inv ≫
        HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat)
    infer_instance
  have : IsIso ((DerivedCategory.Q (C := C)).map s.hom) :=
    Localization.inverts (DerivedCategory.Q (C := C))
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) s.hom
      (inferInstanceAs (QuasiIso s.hom))
  let eQ : (DerivedCategory.singleFunctor C 0).obj A ≅
      (DerivedCategory.Q (C := C)).obj L.obj :=
    asIso ((DerivedCategory.Q (C := C)).map s.hom)
  let e : (DerivedCategory.Plus.singleFunctor C 0).obj A ≅
      DerivedCategory.Plus.Q.obj L :=
    DerivedCategory.Plus.ι.preimageIso
      ((DerivedCategory.Plus.singleFunctorιIso C 0).app A ≪≫ eQ ≪≫
        ((DerivedCategory.Plus.QCompιIso C).app L).symm)
  have : ∀ n : ℤ, Injective (L.obj.X n) := fun _ => inferInstance
  have : IsIso (F.rightDerivedFunctorPlusUnit.app L) :=
    F.rightDerivedFunctorPlusUnit_isIso_of_injective L
  exact DerivedCategory.Plus.ι.mapIso
      (F.rightDerivedFunctorPlus.mapIso e ≪≫
        (asIso (F.rightDerivedFunctorPlusUnit.app L)).symm) ≪≫
    (DerivedCategory.Plus.QCompιIso D).app (F.mapCochainComplexPlus.obj L)

/-- Cohomology of the actual total right-derived object is the homology of
the functor applied to the given extended injective resolution. -/
def rightDerivedFunctorPlusHomologyIso (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D n).obj
      (F.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor C 0).obj A)) ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (I.cocomplex.extend ComplexShape.embeddingUpNat)).homology n :=
  (DerivedCategory.homologyFunctor D n).mapIso (I.rightDerivedFunctorPlusIso F) ≪≫
    (DerivedCategory.homologyFunctorFactors D n).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (I.cocomplex.extend ComplexShape.embeddingUpNat))

end CategoryTheory.InjectiveResolution
