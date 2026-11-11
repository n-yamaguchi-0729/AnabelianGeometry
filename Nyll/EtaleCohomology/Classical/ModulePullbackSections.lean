/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Classical.ModuleExtCohomology
public import Nyll.EtaleCohomology.Classical.ModuleExtPullback
public import Nyll.EtaleCohomology.Classical.ModuleGlobalSectionsComplex
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Classical.PullbackCohomologySections
public import Nyll.EtaleCohomology.Classical.SheafH0TerminalTransport
public import Nyll.EtaleCohomology.Sites.PullbackSections
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# The actual module pullback on global sections

The native global-section functor evaluates at a chosen terminal object of
the small étale site. Its canonical comparison with the identity étale object
transports the original adjunction-unit section map to a natural transformation
between the native global-section functors. The original module Hom comparison
intertwines this transformation with the already constructed source morphism
for geometric pullback.
-/

@[expose] public section

noncomputable section

universe u w w'

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

private theorem mapPrecomp_mk₀
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasExt.{u} C] [HasExt.{u} D] (L : C ⥤ D) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A F : C} {B : D} (b : B ⟶ L.obj A) (a : A ⟶ F) :
    (Ext.mk₀ b).comp ((Ext.mk₀ a).mapExactFunctor L) (zero_add 0) =
      (Ext.mk₀ (b ≫ L.map a) : Ext.{u} B (L.obj F) 0) := by
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- The canonical terminal-object comparison identifies native global sections
with sections at the identity étale object. -/
def etaleModuleGlobalSectionsIdentityIso :
    (sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ X.Etale)) ≅
      (sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
        (op (Scheme.Etale.mk (𝟙 X))) :=
  (sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).mapIso
    (terminalIsTerminal.uniqueUpToIso
      (MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) X)).symm.op

private theorem identityIso_hom_zero
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (x : etaleCohomology X R F 0) :
    (etaleModuleGlobalSectionsIdentityIso X R).hom.app F
        (Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u} F terminalIsTerminal x) =
      Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u} F
        (MorphismProperty.Over.mkIdTerminal
          (show MorphismProperty Scheme.{u} from @Etale) X) x :=
  sheafH0_restriction
    (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F)
    (MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X) terminalIsTerminal
    (terminalIsTerminal.uniqueUpToIso
      (MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) X)).inv x

theorem etaleModuleIntegerHomSectionsIso_down_zero
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (a : etaleFreeIntegerModuleSheaf X R ⟶ F) :
    ((etaleModuleIntegerHomSectionsIso X R).hom.app F a).down =
      Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u} F terminalIsTerminal
        (etaleModuleExtCohomologyMap X R F 0 (Ext.mk₀ a)) := by
  let U := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let Z : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))
  let b : Z ⟶ U.obj F := etaleModuleIntegerHomForgetEquiv X R F a
  let v : (Z ⟶ U.obj F) → (U.obj F).obj.obj (op (⊤_ X.Etale)) :=
    ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u}
      terminalIsTerminal).homAddEquiv (AddCommGrpCat.of (ULift.{u} ℤ)) (U.obj F)).trans
        (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  have hb : (Ext.addEquiv₀ (Ext.mk₀ b) : Z ⟶ U.obj F) = b :=
    (Ext.addEquiv₀ : Ext.{u} Z (U.obj F) 0 ≃+ (Z ⟶ U.obj F)).apply_symm_apply b
  have h : (Ext.addEquiv₀ (etaleModuleExtCohomologyMap X R F 0 (Ext.mk₀ a)) :
      Z ⟶ U.obj F) = b :=
    (congrArg (fun e : Ext.{u} Z (U.obj F) 0 => Ext.addEquiv₀ e)
      (etaleModuleExtCohomologyMap_mk₀ X R a)).trans hb
  change v b = v (Ext.addEquiv₀ (etaleModuleExtCohomologyMap X R F 0 (Ext.mk₀ a)))
  exact congrArg v h.symm

variable {X} {Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual adjunction unit pulls sections back between the identity étale objects. -/
def identitySectionsPullback :
    (sheafSections Y.smallEtaleTopology (ModuleCat.{u} R)).obj
        (op (Scheme.Etale.mk (𝟙 Y))) ⟶
      etalePullback f R ⋙
        (sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
          (op (Scheme.Etale.mk (𝟙 X))) where
  app F := etalePullbackGlobalSectionsMap f R F
  naturality F G a := by
    change a.hom.app (op (Scheme.Etale.mk (𝟙 Y))) ≫
        etalePullbackGlobalSectionsMap f R G =
      etalePullbackGlobalSectionsMap f R F ≫
        ((etalePullback f R).map a).hom.app (op (Scheme.Etale.mk (𝟙 X)))
    exact (etalePullbackSectionMap_naturality f R (F := F) (G := G) a
      (U := Scheme.Etale.mk (𝟙 X)) (V := Scheme.Etale.mk (𝟙 Y)) f
      ((Category.comp_id f).trans (Category.id_comp f).symm)).symm

/-- The actual adjunction-unit pullback on native global sections, with both
canonical terminal-object comparisons retained. -/
def etaleModuleGlobalSectionsPullback :
    (sheafSections Y.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ Y.Etale)) ⟶
      etalePullback f R ⋙
        (sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ X.Etale)) :=
  (etaleModuleGlobalSectionsIdentityIso Y R).hom ≫ identitySectionsPullback R f ≫
    Functor.whiskerLeft (etalePullback f R) (etaleModuleGlobalSectionsIdentityIso X R).inv

private theorem globalSectionsPullback_zero
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R))
    (x : etaleCohomology Y R F 0) :
    (etaleModuleGlobalSectionsPullback R f).app F
        (Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u} F terminalIsTerminal x) =
      Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u}
        ((etalePullback f R).obj F) terminalIsTerminal
          (etaleCohomologyPullbackMap f R F 0 x) := by
  let eY := (etaleModuleGlobalSectionsIdentityIso Y R).app F
  let eX := (etaleModuleGlobalSectionsIdentityIso X R).app ((etalePullback f R).obj F)
  let t := Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u}
    ((etalePullback f R).obj F) terminalIsTerminal (etaleCohomologyPullbackMap f R F 0 x)
  have hY := identityIso_hom_zero Y R F x
  have hX := identityIso_hom_zero X R ((etalePullback f R).obj F)
    (etaleCohomologyPullbackMap f R F 0 x)
  have h : etalePullbackGlobalSectionsMap f R F
      (eY.hom (Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u}
        F terminalIsTerminal x)) = eX.hom t :=
    (congrArg (etalePullbackGlobalSectionsMap f R F) hY).trans
      ((etaleCohomologyPullbackMap_zero_globalSections f R F x).symm.trans hX.symm)
  change eX.inv (etalePullbackGlobalSectionsMap f R F
    (eY.hom (Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u}
      F terminalIsTerminal x))) = t
  exact (congrArg eX.inv h).trans (ConcreteCategory.congr_hom eX.hom_inv_id t)

/-- The original module Hom comparison intertwines the actual source morphism
for pullback with the native global-section transformation. -/
theorem etaleModuleIntegerHomSectionsIso_pullback
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R))
    (a : etaleFreeIntegerModuleSheaf Y R ⟶ F) :
    ((etaleModuleIntegerHomSectionsIso X R).hom.app ((etalePullback f R).obj F)
      (etaleModuleFreeIntegerPullbackHom f R ≫ (etalePullback f R).map a)).down =
      (etaleModuleGlobalSectionsPullback R f).app F
        (((etaleModuleIntegerHomSectionsIso Y R).hom.app F a).down) := by
  let b := etaleModuleFreeIntegerPullbackHom f R ≫ (etalePullback f R).map a
  have hp := etaleModuleExtCohomologyMap_pullback f R F 0 (Ext.mk₀ a)
  have hm := mapPrecomp_mk₀ (etalePullback f R)
    (etaleModuleFreeIntegerPullbackHom f R) a
  have he : etaleModuleExtCohomologyMap X R ((etalePullback f R).obj F) 0 (Ext.mk₀ b) =
      etaleCohomologyPullbackMap f R F 0 (etaleModuleExtCohomologyMap Y R F 0 (Ext.mk₀ a)) :=
    (congrArg (etaleModuleExtCohomologyMap X R ((etalePullback f R).obj F) 0) hm).symm.trans hp
  have hpoint := congrArg
    (Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u}
      ((etalePullback f R).obj F) terminalIsTerminal) he
  exact (etaleModuleIntegerHomSectionsIso_down_zero X R ((etalePullback f R).obj F) b).trans
    (hpoint.trans ((globalSectionsPullback_zero R f F
      (etaleModuleExtCohomologyMap Y R F 0 (Ext.mk₀ a))).symm.trans
        (congrArg ((etaleModuleGlobalSectionsPullback R f).app F)
          (etaleModuleIntegerHomSectionsIso_down_zero Y R F a).symm)))

end EtaleCohomology
