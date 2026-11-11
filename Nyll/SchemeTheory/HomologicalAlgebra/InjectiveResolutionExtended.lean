/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Naturality of the original extended resolution augmentation

The existing zero-extension of the resolution augmentation commutes with
the actual zero-extension of a lifted map. The only extra comparison is
naturality of the existing extension/single-complex isomorphism.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Limits

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The embedding of nonnegative cochain degrees into the integers preserves zero. -/
theorem embeddingUpNat_zero :
    ComplexShape.embeddingUpNat.f (0 : ℕ) = (0 : ℤ) := rfl

private theorem extendSingleIso_inv_naturality
    {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι']
    {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (i : ι) (j : ι') (h : e.f i = j)
    {F G : C} (f : F ⟶ G) :
    (HomologicalComplex.extendSingleIso e F i j h).inv ≫
      HomologicalComplex.extendMap ((HomologicalComplex.single C c i).map f) e =
    (HomologicalComplex.single C c' j).map f ≫
      (HomologicalComplex.extendSingleIso e G i j h).inv := by
  apply HomologicalComplex.from_single_hom_ext
  change (HomologicalComplex.extendSingleIso e F i j h).inv.f j ≫
      (HomologicalComplex.extendMap ((HomologicalComplex.single C c i).map f) e).f j =
    ((HomologicalComplex.single C c' j).map f).f j ≫
      (HomologicalComplex.extendSingleIso e G i j h).inv.f j
  simp only [HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f _ e h,
    HomologicalComplex.single_map_f_self, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- The original zero-extended augmentation, used by both Ext and native
derived-functor resolution computations. -/
def extendedAugmentation {F : C} (I : InjectiveResolution F) :
    (CochainComplex.singleFunctor C 0).obj F ⟶
      I.cocomplex.extend ComplexShape.embeddingUpNat :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0
    embeddingUpNat_zero).inv ≫
    HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat

instance {F : C} (I : InjectiveResolution F) : QuasiIso I.extendedAugmentation := by
  change QuasiIso
    ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0
      embeddingUpNat_zero).inv ≫
      HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat)
  infer_instance

/-- Zero-extension preserves the original augmentation square of any
actual lifted map of injective resolutions. -/
theorem extendedAugmentation_naturality {F G : C} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι ≫ φ = (CochainComplex.single₀ C).map f ≫ J.ι) :
    I.extendedAugmentation ≫ HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat =
      (CochainComplex.singleFunctor C 0).map f ≫ J.extendedAugmentation := by
  let E := ComplexShape.embeddingUpNat.extendFunctor C
  let sF : (CochainComplex.singleFunctor C 0).obj F ⟶
      E.obj ((CochainComplex.single₀ C).obj F) :=
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0
      embeddingUpNat_zero).inv
  let sG : (CochainComplex.singleFunctor C 0).obj G ⟶
      E.obj ((CochainComplex.single₀ C).obj G) :=
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0
      embeddingUpNat_zero).inv
  have hs : sF ≫ E.map ((CochainComplex.single₀ C).map f) =
      (CochainComplex.singleFunctor C 0).map f ≫ sG :=
    extendSingleIso_inv_naturality ComplexShape.embeddingUpNat 0 0 embeddingUpNat_zero f
  have hE : E.map I.ι ≫ E.map φ =
      E.map ((CochainComplex.single₀ C).map f) ≫ E.map J.ι :=
    (E.map_comp I.ι φ).symm.trans
      ((congrArg E.map hφ).trans (E.map_comp ((CochainComplex.single₀ C).map f) J.ι))
  change (sF ≫ E.map I.ι) ≫ E.map φ =
    (CochainComplex.singleFunctor C 0).map f ≫ (sG ≫ E.map J.ι)
  calc
    (sF ≫ E.map I.ι) ≫ E.map φ = sF ≫ (E.map I.ι ≫ E.map φ) :=
      Category.assoc _ _ _
    _ = sF ≫ (E.map ((CochainComplex.single₀ C).map f) ≫ E.map J.ι) :=
      congrArg (fun a => sF ≫ a) hE
    _ = (sF ≫ E.map ((CochainComplex.single₀ C).map f)) ≫ E.map J.ι :=
      (Category.assoc _ _ _).symm
    _ = ((CochainComplex.singleFunctor C 0).map f ≫ sG) ≫ E.map J.ι :=
      congrArg (fun a => a ≫ E.map J.ι) hs
    _ = (CochainComplex.singleFunctor C 0).map f ≫ (sG ≫ E.map J.ι) :=
      Category.assoc _ _ _

/-- In particular, the existing canonical lifted map commutes with the
actual extended augmentations. -/
theorem extendedAugmentation_desc {F G : C} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) :
    I.extendedAugmentation ≫ HomologicalComplex.extendMap (desc f J I)
        ComplexShape.embeddingUpNat =
      (CochainComplex.singleFunctor C 0).map f ≫ J.extendedAugmentation :=
  extendedAugmentation_naturality f I J (desc f J I) (desc_commutes f J I)

end CategoryTheory.InjectiveResolution
