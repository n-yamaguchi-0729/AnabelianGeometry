/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.NatInjectiveResolution
public import Nyll.SchemeTheory.HomologicalAlgebra.RightDerivedFunctorPlusResolution
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Native derived global sections on the small étale site

Global sections of bounded below complexes are derived by the native
`Functor.rightDerivedFunctorPlus`. A given actual injective resolution computes
these functors through its augmentation. For abelian sheaves the homology is
identified with the existing classical `Sheaf.H` by the proved resolution
comparison.

For module sheaves the construction takes place in the actual derived category
of modules. Comparison with classical cohomology of the underlying abelian
sheaf additionally needs its global-section acyclicity; it is not assumed or
asserted here. No cohomological finiteness or perfection is asserted.
-/

@[expose] public section

noncomputable section

universe u wS wA wM

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

section Abelian

variable (X : Scheme.{u})
  [HasDerivedCategory.{wS} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
  [HasDerivedCategory.{wA} AddCommGrpCat.{u}]

/-- The actual right-derived functor of abelian global sections on the
bounded below derived category of the small étale site. -/
def etaleAbelianDerivedGlobalSections :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u} :=
  ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (op (⊤_ X.Etale))).rightDerivedFunctorPlus

/-- The given abelian injective resolution, through its actual augmentation,
computes the native derived global-section object. -/
def etaleAbelianDerivedGlobalSectionsResolutionIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (I : InjectiveResolution F) :
    DerivedCategory.Plus.ι.obj
      ((etaleAbelianDerivedGlobalSections X).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≅
      DerivedCategory.Q.obj
        ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (I.cocomplex.extend ComplexShape.embeddingUpNat)) :=
  I.rightDerivedFunctorPlusIso
    ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (op (⊤_ X.Etale)))

/-- The original classical étale cohomology groups are the actual homology
of native derived abelian global sections. -/
def etaleAbelianCohomologyDerivedGlobalSectionsEquiv
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u} F n ≃+
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (n : ℤ)).obj
        ((etaleAbelianDerivedGlobalSections X).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  let I := injectiveResolution F
  let Γ : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op (⊤_ X.Etale))
  let K : CochainComplex AddCommGrpCat.{u} ℕ :=
    (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let e : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (n : ℤ)).obj
      ((etaleAbelianDerivedGlobalSections X).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≅ K.homology n :=
    I.rightDerivedFunctorPlusHomologyIso Γ (n : ℤ) ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
        (ComplexShape.up ℤ) (n : ℤ)).mapIso
          (etaleGlobalSectionsExtendIso X I.cocomplex) ≪≫
      K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl
  exact (etaleAbelianCohomologyNatResolutionEquiv X F I n).trans
    e.symm.addCommGroupIsoToAddEquiv

end Abelian

section Module

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- Module-valued global sections are additive, through the canonical
sheaf evaluation comparison. -/
instance etaleModuleGlobalSections_additive :
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (op (⊤_ X.Etale))).Additive :=
  Functor.additive_of_iso
    (sheafSectionsNatIsoEvaluation X.smallEtaleTopology (ModuleCat.{u} R)
      (X := ⊤_ X.Etale)).symm

variable
  [HasDerivedCategory.{wS} (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))]
  [HasDerivedCategory.{wM} (ModuleCat.{u} R)]

/-- The actual module-valued right-derived global-section functor on the
bounded below derived category of the small étale site. -/
def etaleModuleDerivedGlobalSections :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) ⥤
      DerivedCategory.Plus (ModuleCat.{u} R) :=
  ((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
    (op (⊤_ X.Etale))).rightDerivedFunctorPlus

/-- A given module injective resolution computes actual native module-valued
derived global sections through its augmentation. -/
def etaleModuleDerivedGlobalSectionsResolutionIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (I : InjectiveResolution F) :
    DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections X R).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≅
      DerivedCategory.Q.obj
        ((((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
          (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (I.cocomplex.extend ComplexShape.embeddingUpNat)) :=
  I.rightDerivedFunctorPlusIso
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (op (⊤_ X.Etale)))

/-- The actual homology modules of module-valued derived global sections are
computed by global sections of the given extended module injective resolution. -/
def etaleModuleDerivedGlobalSectionsHomologyIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (I : InjectiveResolution F) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).obj
      ((etaleModuleDerivedGlobalSections X R).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≅
      ((((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
        (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (I.cocomplex.extend ComplexShape.embeddingUpNat)).homology n :=
  I.rightDerivedFunctorPlusHomologyIso
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (op (⊤_ X.Etale))) n

end Module

end EtaleCohomology
