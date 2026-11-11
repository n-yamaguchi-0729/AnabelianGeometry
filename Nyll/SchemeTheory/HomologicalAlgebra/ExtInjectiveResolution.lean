/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.HomologicalAlgebra.HomComplexPostcomp
public import Nyll.SchemeTheory.HomologicalAlgebra.InjectiveResolutionExtended
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Whiskering

/-!
# Ext computed on an actual injective resolution

This is the shared generic proof formerly private to the classical étale
injective-resolution comparison. The given augmentation supplies the derived
isomorphism, and bounded-below injectives supply the actual K-injectivity.
-/

@[expose] public section

noncomputable section

universe w v uC

open CategoryTheory Limits CochainComplex

namespace CategoryTheory.Abelian

/-- The additive equivalence on morphisms induced by two object isomorphisms. -/
def homCongrAddEquiv {C : Type uC} [Category.{v} C] [Preadditive C]
    {A B A' B' : C} (e : A ≅ A') (f : B ≅ B') : (A ⟶ B) ≃+ (A' ⟶ B') where
  toEquiv := Iso.homCongr e f
  map_add' a b := by
    change e.inv ≫ (a + b) ≫ f.hom = (e.inv ≫ a ≫ f.hom) + (e.inv ≫ b ≫ f.hom)
    rw [Preadditive.add_comp, Preadditive.comp_add]

/-- Derived morphisms into a K-injective complex compute the actual Hom-complex homology. -/
def derivedHomComplexHomologyEquiv
    {C : Type uC} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (K L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ) :
    (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦n⟧) ≃+
      (CochainComplex.HomComplex K L).homology n := by
  let qK : HomotopyCategory C (ComplexShape.up ℤ) :=
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K
  let qL : HomotopyCategory C (ComplexShape.up ℤ) :=
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧)
  let eK : (DerivedCategory.Qh (C := C)).obj qK ≅ DerivedCategory.Q.obj K :=
    (DerivedCategory.quotientCompQhIso C).app K
  let eL : (DerivedCategory.Qh (C := C)).obj qL ≅ (DerivedCategory.Q.obj L)⟦n⟧ :=
    (DerivedCategory.quotientCompQhIso C).app (L⟦n⟧) ≪≫
      ((DerivedCategory.Q (C := C)).commShiftIso n).app L
  let eQ : (qK ⟶ qL) ≃+
      ((DerivedCategory.Qh (C := C)).obj qK ⟶ (DerivedCategory.Qh (C := C)).obj qL) :=
    AddEquiv.ofBijective (DerivedCategory.Qh (C := C)).mapAddHom
      (CochainComplex.IsKInjective.Qh_map_bijective qK (L⟦n⟧))
  exact (homCongrAddEquiv eK eL).symm.trans
    (eQ.symm.trans
      ((HomComplex.CohomologyClass.homAddEquiv (K := K) (L := L) (n := n)).symm.trans
        (HomComplex.homologyAddEquiv K L n).symm))

/-- The derived-Hom comparison preserves actual postcomposition. -/
theorem derivedHomComplexHomologyEquiv_symm_naturality
    {C : Type uC} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (A : C) {L M : CochainComplex C ℤ} [L.IsKInjective] [M.IsKInjective]
    (φ : L ⟶ M) (n : ℤ)
    (z : (CochainComplex.HomComplex
      ((CochainComplex.singleFunctor C 0).obj A) L).homology n) :
    (derivedHomComplexHomologyEquiv ((CochainComplex.singleFunctor C 0).obj A) M n).symm
        (HomologicalComplex.homologyMap ((homFromSingleFunctor A).map φ) n z) =
      (derivedHomComplexHomologyEquiv ((CochainComplex.singleFunctor C 0).obj A) L n).symm z ≫
        (DerivedCategory.Q.map φ)⟦n⟧' := by
  let K := (CochainComplex.singleFunctor C 0).obj A
  let eK := (DerivedCategory.quotientCompQhIso C).app K
  let eShift := Functor.isoWhiskerLeft (CategoryTheory.shiftFunctor (CochainComplex C ℤ) n)
      (DerivedCategory.quotientCompQhIso C) ≪≫
    (DerivedCategory.Q (C := C)).commShiftIso n
  change eK.inv ≫ DerivedCategory.Qh.map
      (HomComplex.CohomologyClass.toHom
        (HomComplex.homologyAddEquiv K M n
          (HomologicalComplex.homologyMap ((homFromSingleFunctor A).map φ) n z))) ≫
      (eShift.app M).hom =
    (eK.inv ≫ DerivedCategory.Qh.map
      (HomComplex.CohomologyClass.toHom (HomComplex.homologyAddEquiv K L n z)) ≫
        (eShift.app L).hom) ≫ (DerivedCategory.Q.map φ)⟦n⟧'
  have hc : HomComplex.homologyAddEquiv K M n
      (HomologicalComplex.homologyMap ((homFromSingleFunctor A).map φ) n z) =
      HomComplex.cohomologyClassPostcomp φ n (HomComplex.homologyAddEquiv K L n z) :=
    HomComplex.homologyAddEquiv_homFromSingle_postcomp φ n A z
  refine (congrArg (fun a : HomComplex.CohomologyClass K M n =>
    eK.inv ≫ DerivedCategory.Qh.map (HomComplex.CohomologyClass.toHom a) ≫
      (eShift.app M).hom) hc).trans ?_
  rw [HomComplex.cohomologyClassPostcomp_toHom, Functor.map_comp]
  have h := eShift.hom.naturality φ
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map (φ⟦n⟧')) ≫
      (eShift.app M).hom = (eShift.app L).hom ≫ (DerivedCategory.Q.map φ)⟦n⟧' at h
  simpa only [Category.assoc] using
    congrArg (fun a => eK.inv ≫ DerivedCategory.Qh.map
      (HomComplex.CohomologyClass.toHom (HomComplex.homologyAddEquiv K L n z)) ≫ a) h

/-- Actual Ext is computed by the Hom complex of the given injective resolution. -/
def extResolutionHomologyEquiv
    {C : Type uC} [Category.{v} C] [Abelian C] [HasDerivedCategory C] [HasExt.{w} C]
    (A : C) {F : C} (I : InjectiveResolution F) (n : ℕ) :
    Abelian.Ext.{w} A F n ≃+
      (CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj A)
        (I.cocomplex.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) := by
  let L : CochainComplex C ℤ := I.cocomplex.extend ComplexShape.embeddingUpNat
  let s : (CochainComplex.singleFunctor C 0).obj F ⟶ L :=
    I.extendedAugmentation
  let e : (DerivedCategory.singleFunctor C 0).obj F ≅ DerivedCategory.Q.obj L :=
    asIso (DerivedCategory.Q.map s)
  let en : ((DerivedCategory.singleFunctor C 0).obj F)⟦(n : ℤ)⟧ ≅
      (DerivedCategory.Q.obj L)⟦(n : ℤ)⟧ :=
    (CategoryTheory.shiftFunctor (DerivedCategory C) (n : ℤ)).mapIso e
  exact Abelian.Ext.homAddEquiv.trans
    ((homCongrAddEquiv (Iso.refl ((DerivedCategory.singleFunctor C 0).obj A)) en).trans
      (derivedHomComplexHomologyEquiv ((CochainComplex.singleFunctor C 0).obj A) L (n : ℤ)))

/-- The resolution comparison recovers the original Ext morphism followed by the augmentation. -/
theorem extResolutionHomologyEquiv_toDerived
    {C : Type uC} [Category.{v} C] [Abelian C] [HasDerivedCategory C] [HasExt.{w} C]
    (A : C) {F : C} (I : InjectiveResolution F) (n : ℕ) (x : Ext.{w} A F n) :
    (derivedHomComplexHomologyEquiv ((CochainComplex.singleFunctor C 0).obj A)
      (I.cocomplex.extend ComplexShape.embeddingUpNat) (n : ℤ)).symm
        (extResolutionHomologyEquiv A I n x) =
      x.hom ≫ (DerivedCategory.Q.map I.extendedAugmentation)⟦(n : ℤ)⟧' := by
  let L : CochainComplex C ℤ := I.cocomplex.extend ComplexShape.embeddingUpNat
  let s : (CochainComplex.singleFunctor C 0).obj F ⟶ L := I.extendedAugmentation
  let e := asIso (DerivedCategory.Q.map s)
  let en := (CategoryTheory.shiftFunctor (DerivedCategory C) (n : ℤ)).mapIso e
  change (derivedHomComplexHomologyEquiv ((CochainComplex.singleFunctor C 0).obj A)
      L (n : ℤ)).symm
    ((derivedHomComplexHomologyEquiv ((CochainComplex.singleFunctor C 0).obj A)
      L (n : ℤ)) ((homCongrAddEquiv (Iso.refl _) en) x.hom)) = _
  rw [AddEquiv.symm_apply_apply]
  change (𝟙 _) ≫ x.hom ≫ en.hom = _
  rw [Category.id_comp]
  rfl

/-- The Ext-resolution comparison respects every actual lifted chain map
that commutes with the original extended augmentations. -/
theorem extResolutionHomologyEquiv_naturality
    {C : Type uC} [Category.{v} C] [Abelian C] [HasDerivedCategory C] [HasExt.{w} C]
    (A : C) {F G : C} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex.extend ComplexShape.embeddingUpNat ⟶
      J.cocomplex.extend ComplexShape.embeddingUpNat)
    (hφ : I.extendedAugmentation ≫ φ =
      (CochainComplex.singleFunctor C 0).map f ≫
        J.extendedAugmentation)
    (n : ℕ) (x : Ext.{w} A F n) :
    extResolutionHomologyEquiv A J n (x.comp (Ext.mk₀ f) (add_zero n)) =
      HomologicalComplex.homologyMap ((homFromSingleFunctor A).map φ) (n : ℤ)
        (extResolutionHomologyEquiv A I n x) := by
  let sI : (CochainComplex.singleFunctor C 0).obj F ⟶
      I.cocomplex.extend ComplexShape.embeddingUpNat := I.extendedAugmentation
  let sJ : (CochainComplex.singleFunctor C 0).obj G ⟶
      J.cocomplex.extend ComplexShape.embeddingUpNat := J.extendedAugmentation
  have hpost :
      (derivedHomComplexHomologyEquiv ((CochainComplex.singleFunctor C 0).obj A)
          (J.cocomplex.extend ComplexShape.embeddingUpNat) (n : ℤ)).symm
        (HomologicalComplex.homologyMap ((homFromSingleFunctor A).map φ) (n : ℤ)
          (extResolutionHomologyEquiv A I n x)) =
      (derivedHomComplexHomologyEquiv ((CochainComplex.singleFunctor C 0).obj A)
          (I.cocomplex.extend ComplexShape.embeddingUpNat) (n : ℤ)).symm
        (extResolutionHomologyEquiv A I n x) ≫
          (DerivedCategory.Q.map φ)⟦(n : ℤ)⟧' :=
    derivedHomComplexHomologyEquiv_symm_naturality A
      (L := I.cocomplex.extend ComplexShape.embeddingUpNat)
      (M := J.cocomplex.extend ComplexShape.embeddingUpNat) φ (n : ℤ)
      (extResolutionHomologyEquiv A I n x)
  apply (derivedHomComplexHomologyEquiv ((CochainComplex.singleFunctor C 0).obj A)
    (J.cocomplex.extend ComplexShape.embeddingUpNat) (n : ℤ)).symm.injective
  refine Eq.trans ?_ hpost.symm
  rw [extResolutionHomologyEquiv_toDerived, extResolutionHomologyEquiv_toDerived,
    Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀]
  have hQ : DerivedCategory.Q.map sI ≫ DerivedCategory.Q.map φ =
      (DerivedCategory.singleFunctor C 0).map f ≫ DerivedCategory.Q.map sJ := by
    rw [← Functor.map_comp]
    exact (congrArg DerivedCategory.Q.map hφ).trans
      (DerivedCategory.Q.map_comp ((CochainComplex.singleFunctor C 0).map f) sJ)
  have hn := congrArg ((CategoryTheory.shiftFunctor (DerivedCategory C) (n : ℤ)).map) hQ
  simp only [Functor.map_comp] at hn
  simpa only [Category.assoc] using congrArg (fun a => x.hom ≫ a) hn.symm

/-- The Ext-resolution comparison is natural for the existing canonical
lift of the original coefficient morphism, with no comparison premise. -/
theorem extResolutionHomologyEquiv_desc_naturality
    {C : Type uC} [Category.{v} C] [Abelian C] [HasDerivedCategory C] [HasExt.{w} C]
    (A : C) {F G : C} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) (n : ℕ)
    (x : Ext.{w} A F n) :
    extResolutionHomologyEquiv A J n (x.comp (Ext.mk₀ f) (add_zero n)) =
      HomologicalComplex.homologyMap
        ((homFromSingleFunctor A).map
          (HomologicalComplex.extendMap (InjectiveResolution.desc f J I)
            ComplexShape.embeddingUpNat)) (n : ℤ)
        (extResolutionHomologyEquiv A I n x) :=
  extResolutionHomologyEquiv_naturality A f I J
    (HomologicalComplex.extendMap (InjectiveResolution.desc f J I)
      ComplexShape.embeddingUpNat)
    (InjectiveResolution.extendedAugmentation_desc f I J) n x

end CategoryTheory.Abelian
