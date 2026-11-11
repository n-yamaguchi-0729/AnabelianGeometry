/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.H1FiniteCover
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The original integer section evaluates actual H⁰ classes

The morphism corresponding to an actual degree-zero Ext class sends the
original constant integer section one to the restriction of the original
global section. This identifies the quotient section in a pulled-back
extension with the original cohomology section on every étale object.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleFundamentalGroups.Cohomology

/-- Evaluation on the original integer section one recovers the actual
degree-zero section after the original terminal restriction. -/
theorem cohomologyZero_integerUnitSection
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : Sheaf.H.{u} F 0) (V : X.Etale) :
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    (Ext.addEquiv₀ a).hom.app (op V)
        ((integerUnitSection X).app (op V) PUnit.unit) =
      F.obj.map (hT.from V).op (Sheaf.H.equiv₀.{u} F hT a) := by
  intro hT
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let Z := AddCommGrpCat.of (ULift.{u} ℤ)
  let C := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj Z
  let q : C ⟶ F := Ext.addEquiv₀ a
  let η : Z ⟶ C.obj.obj (op T) :=
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).unit.app Z
  let m : V ⟶ T := hT.from V
  have hη : η =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj Z)).app (op T) := by
    have h := Adjunction.comp_unit_app
      (constantPresheafAdj AddCommGrpCat.{u} hT)
      (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u}) Z
    change η = 𝟙 Z ≫
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj Z)).app (op T) at h
    exact h.trans (Category.id_comp _)
  have htop : q.hom.app (op T) ((integerUnitSection X).app (op T) PUnit.unit) =
      Sheaf.H.equiv₀.{u} F hT a := by
    change q.hom.app (op T)
        ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj Z)).app
          (op T) (ULift.up (1 : ℤ))) =
      q.hom.app (op T) (η (ULift.up (1 : ℤ)))
    exact congrArg (q.hom.app (op T))
      (ConcreteCategory.congr_hom hη (ULift.up (1 : ℤ))).symm
  have hunit : C.obj.map m.op ((integerUnitSection X).app (op T) PUnit.unit) =
      (integerUnitSection X).app (op V) PUnit.unit :=
    (ConcreteCategory.congr_hom ((integerUnitSection X).naturality m.op) PUnit.unit).symm
  have hn : q.hom.app (op V)
      (C.obj.map m.op ((integerUnitSection X).app (op T) PUnit.unit)) =
        F.obj.map m.op
          (q.hom.app (op T) ((integerUnitSection X).app (op T) PUnit.unit)) :=
    ConcreteCategory.congr_hom (q.hom.naturality m.op)
      ((integerUnitSection X).app (op T) PUnit.unit)
  change q.hom.app (op V) ((integerUnitSection X).app (op V) PUnit.unit) =
    F.obj.map m.op (Sheaf.H.equiv₀.{u} F hT a)
  exact (congrArg (q.hom.app (op V)) hunit.symm).trans
    (hn.trans (congrArg (F.obj.map m.op) htop))

end EtaleFundamentalGroups.Cohomology
