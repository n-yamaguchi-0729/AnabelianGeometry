/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantCoefficientUnit
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.ModuleExtCohomology
public import Nyll.EtaleCohomology.Classical.ModuleExtPullback
public import Nyll.EtaleCohomology.Classical.ModuleGlobalSectionsComplex
public import Nyll.EtaleCohomology.Classical.ModulePullbackSections
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Sites.ConstantPullback
public import Nyll.EtaleCohomology.Sites.ConstantPullbackSections
public import Nyll.EtaleCohomology.Sites.PullbackSections
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The constant coefficient source respects actual pullback

The existing corepresenting isomorphism preserves constant sections. The
original inverse-image adjunction therefore identifies its source map with
the canonical constant-sheaf comparison. The resulting Ext square uses the
original classical pullback in every degree.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

private theorem constantHom_identitySections
    (X : Scheme.{u}) (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (a : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M ⟶ F)
    (x : M) :
    (etaleModuleGlobalSectionsIdentityIso X R).hom.app F
        (((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
          terminalIsTerminal).homEquiv M F a) x) =
      ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
        (op (Scheme.Etale.mk (𝟙 X))) ≫ a.hom.app (op (Scheme.Etale.mk (𝟙 X)))) x := by
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let i : T ⟶ ⊤_ X.Etale :=
    (terminalIsTerminal.uniqueUpToIso
      (MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) X)).inv
  let q : (Functor.const X.Etaleᵒᵖ).obj M ⟶ F.obj :=
    toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M) ≫ a.hom
  have hn : q.app (op (⊤_ X.Etale)) ≫ F.obj.map i.op = q.app (op T) :=
    (q.naturality i.op).symm.trans (Category.id_comp _)
  exact ConcreteCategory.congr_hom hn x

private theorem constantHom_globalSectionsPullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R))
    (a : (constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj M ⟶ F)
    (x : M) :
    ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
      terminalIsTerminal).homEquiv M ((etalePullback f R).obj F)
        (((etalePullbackConstantIso f R).app M).inv ≫ (etalePullback f R).map a)) x =
      (etaleModuleGlobalSectionsPullback R f).app F
        (((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u} R)
          terminalIsTerminal).homEquiv M F a) x) := by
  let U : X.Etale := Scheme.Etale.mk (𝟙 X)
  let V : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  let l : U ⟶ (etaleBaseChange f).obj V :=
    etaleBaseChangeLift f f ((Category.comp_id f).trans (Category.id_comp f).symm)
  let B := (etalePullback f R).obj F
  let b : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M ⟶ B :=
    ((etalePullbackConstantIso f R).app M).inv ≫ (etalePullback f R).map a
  let eX := (etaleModuleGlobalSectionsIdentityIso X R).app B
  let eY := (etaleModuleGlobalSectionsIdentityIso Y R).app F
  let y := ((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u} R)
    terminalIsTerminal).homEquiv M F a) x
  have hX := constantHom_identitySections X R M B b x
  have hY := constantHom_identitySections Y R M F a x
  have hs := Sites.constantSheafHom_pullback_section f (etalePullback f R)
    (etalePullbackPushforwardAdjunction f R) M F a V U l
  have hp := ConcreteCategory.congr_hom hs x
  have ht : eX.hom ((etaleModuleGlobalSectionsPullback R f).app F y) =
      etalePullbackGlobalSectionsMap f R F (eY.hom y) :=
    ConcreteCategory.congr_hom eX.inv_hom_id
      (etalePullbackGlobalSectionsMap f R F (eY.hom y))
  apply eX.toLinearEquiv.injective
  exact hX.trans (hp.trans
    ((congrArg (etalePullbackGlobalSectionsMap f R F) hY.symm).trans ht.symm))

private theorem integerHomSections_constantSource
    (X : Scheme.{u}) (R : Type u) [CommRing R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (a : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (ModuleCat.of R R) ⟶ F) :
    (((etaleModuleIntegerHomSectionsIso X R).hom.app F)
      ((etaleFreeIntegerModuleSheafIsoConstant X R).hom ≫ a)).down =
      ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
        terminalIsTerminal).homEquiv (ModuleCat.of R R) F a) 1 :=
  (etaleModuleIntegerHomSectionsIso_down_zero X R F
    ((etaleFreeIntegerModuleSheafIsoConstant X R).hom ≫ a)).trans
      (etaleFreeIntegerModuleSheafIsoConstant_hom_sections X R F a)

/-- The original free-integer source for module pullback is the actual
constant regular source under the existing corepresenting isomorphisms. -/
theorem etaleFreeIntegerModuleSheafIsoConstant_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R] :
    (etaleFreeIntegerModuleSheafIsoConstant X R).hom ≫
        ((etalePullbackConstantIso f R).app (ModuleCat.of R R)).inv =
      etaleModuleFreeIntegerPullbackHom f R ≫
        (etalePullback f R).map (etaleFreeIntegerModuleSheafIsoConstant Y R).hom := by
  let CY := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)
  let B := (etalePullback f R).obj CY
  let eY := etaleFreeIntegerModuleSheafIsoConstant Y R
  let c := (etalePullbackConstantIso f R).app (ModuleCat.of R R)
  let HX : (etaleFreeIntegerModuleSheaf X R ⟶ B) → B.obj.obj (op (⊤_ X.Etale)) :=
    fun a => (((etaleModuleIntegerHomSectionsIso X R).hom.app B) a).down
  let HY : (etaleFreeIntegerModuleSheaf Y R ⟶ CY) → CY.obj.obj (op (⊤_ Y.Etale)) :=
    fun a => (((etaleModuleIntegerHomSectionsIso Y R).hom.app CY) a).down
  have hy : HY eY.hom =
      ((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u} R)
        terminalIsTerminal).homEquiv (ModuleCat.of R R) CY (𝟙 CY)) 1 :=
    (congrArg HY (Category.comp_id eY.hom)).symm.trans
      (integerHomSections_constantSource Y R CY (𝟙 CY))
  have hmap : c.inv ≫ (etalePullback f R).map (𝟙 CY) = c.inv :=
    (congrArg (fun z : B ⟶ B => c.inv ≫ z)
      ((etalePullback f R).map_id CY)).trans (Category.comp_id c.inv)
  have hs := constantHom_globalSectionsPullback f R (ModuleCat.of R R) CY (𝟙 CY) 1
  have hleft := integerHomSections_constantSource X R B c.inv
  have hright := etaleModuleIntegerHomSectionsIso_pullback R f CY eY.hom
  have hconst := congrArg (fun a =>
    ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
      terminalIsTerminal).homEquiv (ModuleCat.of R R) B a) 1) hmap
  have he : HX ((etaleFreeIntegerModuleSheafIsoConstant X R).hom ≫ c.inv) =
      HX (etaleModuleFreeIntegerPullbackHom f R ≫ (etalePullback f R).map eY.hom) :=
    hleft.trans (hconst.symm.trans (hs.trans
      ((congrArg ((etaleModuleGlobalSectionsPullback R f).app CY) hy.symm).trans
        hright.symm)))
  apply ((etaleModuleIntegerHomSectionsIso X R).app B).addCommGroupIsoToAddEquiv.injective
  exact ULift.ext he

/-- The actual constant-source module Ext comparison commutes with the
original scheme pullback in every degree. -/
theorem etaleConstantModuleExtCohomologyEquiv_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ)
    (x : Ext.{u}
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) F n) :
    etaleConstantModuleExtCohomologyEquiv X R ((etalePullback f R).obj F) n
        ((Ext.mk₀ (((etalePullbackConstantIso f R).app (ModuleCat.of R R)).inv)).comp
          (x.mapExactFunctor (etalePullback f R)) (zero_add n)) =
      etaleCohomologyPullbackMap f R F n
        (etaleConstantModuleExtCohomologyEquiv Y R F n x) := by
  change etaleModuleExtCohomologyEquiv X R ((etalePullback f R).obj F) n
      ((Ext.mk₀ (etaleFreeIntegerModuleSheafIsoConstant X R).hom).comp
        ((Ext.mk₀ (((etalePullbackConstantIso f R).app (ModuleCat.of R R)).inv)).comp
          (x.mapExactFunctor (etalePullback f R)) (zero_add n)) (zero_add n)) = _
  rw [Ext.mk₀_comp_mk₀_assoc, etaleFreeIntegerModuleSheafIsoConstant_pullback]
  rw [← Ext.mk₀_comp_mk₀_assoc, ← Ext.mapExactFunctor_mk₀, ← Ext.mapExactFunctor_comp]
  exact etaleModuleExtCohomologyMap_pullback f R F n
    ((Ext.mk₀ (etaleFreeIntegerModuleSheafIsoConstant Y R).hom).comp x (zero_add n))

end EtaleCohomology
