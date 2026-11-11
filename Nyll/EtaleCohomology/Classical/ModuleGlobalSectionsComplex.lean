/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.DerivedGlobalSections
public import Nyll.EtaleCohomology.Classical.GlobalSectionsComplex
public import Nyll.EtaleCohomology.Classical.ModuleExtCohomology
public import Nyll.SchemeTheory.HomologicalAlgebra.HomFromSingle
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Whiskering

/-!
# The module Hom complex and actual global sections

The existing coefficient adjunction and constant-integer sections comparison
identify the Hom functor from the actual free-integer module sheaf with
underlying global sections. The shared from-single comparison then gives a
natural chain isomorphism for the original module complex.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- A natural additive Hom equivalence identifies the original coyoneda functors. -/
def coyonedaIsoOfNaturalHomEquiv
    {C : Type*} [Category.{v} C] [Preadditive C]
    {D : Type*} [Category.{v} D] [Preadditive D]
    (U : C ⥤ D) (A : C) (B : D)
    (e : ∀ F : C, (A ⟶ F) ≃+ (B ⟶ U.obj F))
    (he : ∀ {F G : C} (a : A ⟶ F) (f : F ⟶ G),
      e G (a ≫ f) = e F a ≫ U.map f) :
    preadditiveCoyoneda.obj (op A) ≅ U ⋙ preadditiveCoyoneda.obj (op B) :=
  NatIso.ofComponents (fun F => (e F).toAddCommGrpIso) (by
    intro F G f
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    change e G (a ≫ f) = e F a ≫ U.map f
    exact he (show A ⟶ F from a) f)

/-- Taking sections commutes with pointwise composition of sheaves. -/
def sheafComposeSectionsIso
    {S : Type*} [Category S] (J : GrothendieckTopology S)
    {A : Type*} [Category A] {B : Type*} [Category B]
    {E : Type*} [Category E] (F : A ⥤ B) [J.HasSheafCompose F]
    (V : B ⥤ E) (T : Sᵒᵖ) :
    sheafCompose J F ⋙ ((sheafSections J B).obj T ⋙ V) ≅
      (sheafSections J A).obj T ⋙ (F ⋙ V) :=
  Iso.refl _

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- Actual module global sections preserve scalar multiples of coefficient
morphisms, by evaluation of the underlying natural transformation. -/
instance etaleModuleGlobalSections_linear :
    Functor.Linear R ((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (op (⊤_ X.Etale))) where
  map_smul _ _ := rfl

/-- The actual coefficient adjunction identifies the module Hom functor
with underlying global sections, followed by the canonical universe lift. -/
def etaleModuleIntegerHomSectionsIso :
    preadditiveCoyoneda.obj (op (etaleFreeIntegerModuleSheaf X R)) ≅
      (sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ X.Etale)) ⋙
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙
          AddCommGrpCat.uliftFunctor.{u + 1, u}) := by
  let U : Sheaf X.smallEtaleTopology (ModuleCat.{u} R) ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R)
  let B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))
  let e : preadditiveCoyoneda.obj (op (etaleFreeIntegerModuleSheaf X R)) ≅
      U ⋙ preadditiveCoyoneda.obj (op B) :=
    coyonedaIsoOfNaturalHomEquiv U (etaleFreeIntegerModuleSheaf X R) B
      (etaleModuleIntegerHomForgetEquiv X R)
      (fun a f => etaleModuleIntegerHomForgetEquiv_naturality X R a f)
  exact e ≪≫ Functor.isoWhiskerLeft U (etaleIntegerHomSectionsIso X) ≪≫
    sheafComposeSectionsIso X.smallEtaleTopology
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
      AddCommGrpCat.uliftFunctor.{u + 1, u} (op (⊤_ X.Etale))

/-- The original module Hom complex identifies naturally with underlying
global sections of the original module complex. -/
def etaleModuleHomFromIntegerSectionsIso :
    homFromSingleFunctor (etaleFreeIntegerModuleSheaf X R) ≅
      (((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ X.Etale))) ⋙
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙
          AddCommGrpCat.uliftFunctor.{u + 1, u})).mapHomologicalComplex (ComplexShape.up ℤ) :=
  homFromSingleIso (etaleFreeIntegerModuleSheaf X R) ≪≫
    NatIso.mapHomologicalComplex (etaleModuleIntegerHomSectionsIso X R) (ComplexShape.up ℤ)

/-- The same chain comparison induces a natural homology comparison with
actual module global sections, using exact coefficient forgetting. -/
def etaleModuleHomologyFromIntegerSectionsIso (n : ℤ) :
    homFromSingleFunctor (etaleFreeIntegerModuleSheaf X R) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) n ≅
      (((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
          (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n ⋙
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙
            AddCommGrpCat.uliftFunctor.{u + 1, u}) := by
  let Γ := (sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ X.Etale))
  let V := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1}
    (ComplexShape.up ℤ) n
  let eV : V.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ H ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n ⋙ V :=
    NatIso.ofComponents (fun K => (K.sc n).mapHomologyIso V) (by
      intro K L φ
      exact ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
          (ComplexShape.up ℤ) n).map φ) V)
  exact Functor.isoWhiskerRight (etaleModuleHomFromIntegerSectionsIso X R) H ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (Γ ⋙ V)) (ComplexShape.up ℤ)).symm H ≪≫
    Functor.associator (Γ.mapHomologicalComplex (ComplexShape.up ℤ))
      (V.mapHomologicalComplex (ComplexShape.up ℤ)) H ≪≫
    Functor.isoWhiskerLeft (Γ.mapHomologicalComplex (ComplexShape.up ℤ)) eV

/-- The homology comparison acts by the original chain comparison followed
by the canonical comparison for exact coefficient forgetting. -/
theorem etaleModuleHomologyFromIntegerSectionsIso_hom_app
    (n : ℤ) (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) ℤ) :
    (etaleModuleHomologyFromIntegerSectionsIso X R n).hom.app K =
      HomologicalComplex.homologyMap
          ((etaleModuleHomFromIntegerSectionsIso X R).hom.app K) n ≫
        ((((((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
          (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).sc n).mapHomologyIso
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙
            AddCommGrpCat.uliftFunctor.{u + 1, u})).hom := by
  let V : ModuleCat.{u} R ⥤ AddCommGrpCat.{u + 1} :=
    forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⋙
      AddCommGrpCat.uliftFunctor.{u + 1, u}
  let P : CochainComplex (ModuleCat.{u} R) ℤ :=
    (((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let a : (homFromSingleFunctor (etaleFreeIntegerModuleSheaf X R)).obj K ⟶
      (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj P :=
    (etaleModuleHomFromIntegerSectionsIso X R).hom.app K
  change HomologicalComplex.homologyMap a n ≫
      (HomologicalComplex.homologyMap
        (𝟙 ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) n ≫
          𝟙 _ ≫ ((P.sc n).mapHomologyIso V).hom) =
    HomologicalComplex.homologyMap a n ≫ ((P.sc n).mapHomologyIso V).hom
  rw [HomologicalComplex.homologyMap_id]
  change HomologicalComplex.homologyMap a n ≫
      (𝟙 ((P.sc n).map V).homology ≫
        𝟙 ((P.sc n).map V).homology ≫ ((P.sc n).mapHomologyIso V).hom) = _
  exact congrArg (fun z => HomologicalComplex.homologyMap a n ≫ z)
    ((Category.id_comp (𝟙 ((P.sc n).map V).homology ≫
      ((P.sc n).mapHomologyIso V).hom)).trans
        (Category.id_comp ((P.sc n).mapHomologyIso V).hom))

end EtaleCohomology
