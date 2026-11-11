/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer

/-!
# Finite descent for filtered colimits of abelian presheaves

A finite degree-one hypercover imposes finitely many matching conditions.
Filtered colimits of abelian groups commute with its multiequalizer, so
descent for this hypercover passes to the presheaf colimit.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.PreOneHypercover

universe u v

variable {C : Type v} [Category.{u} C] {X : C}
  {I : Type u} [SmallCategory I] [IsFiltered I]

/-- The multiequalizer of a finite hypercover remains limiting after taking
a filtered colimit of abelian presheaves. -/
def filteredColimitIsLimitMultifork (E : PreOneHypercover.{u} X)
    [Finite E.I₀] [Finite E.I₁']
    (F : I ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (hF : ∀ i, IsLimit (E.multifork (F.obj i))) :
    IsLimit (E.multifork (colimit F)) := by
  classical
  let : Fintype E.I₀ := Fintype.ofFinite E.I₀
  let : Fintype E.I₁' := Fintype.ofFinite E.I₁'
  let : Fintype E.multicospanShape.L := inferInstanceAs (Fintype E.I₀)
  let : Fintype E.multicospanShape.R := inferInstanceAs (Fintype E.I₁')
  let : FinCategory (WalkingMulticospan E.multicospanShape) := inferInstance
  let Q := F.flip ⋙ (colim : (I ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u})
  have hFlip : IsLimit (E.multifork F.flip) := by
    apply evaluationJointlyReflectsLimits
    intro i
    exact (Multifork.isLimitMapEquiv (E.multifork F.flip)
      ((evaluation I AddCommGrpCat.{u}).obj i)).symm (hF i)
  have hQ : IsLimit (E.multifork Q) := by
    exact Multifork.isLimitMapOfPreserves (E.multifork F.flip)
      (colim : (I ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}) hFlip
  let e : colimit F ≅ Q := colimitFlipIsoCompColim F.flip
  exact (Multifork.isLimitEquivOfIsos
    (E.multifork (colimit F)) (E.multifork Q)
    (e.app (op X))
    (fun i => e.app (op (E.X i)))
    (fun j => e.app (op (E.Y j.2)))
    (fun j => e.hom.naturality (E.p₁ j.2).op)
    (fun j => e.hom.naturality (E.p₂ j.2).op)
    (fun i => (e.hom.naturality (E.f i).op).symm)).symm hQ

end CategoryTheory.PreOneHypercover

namespace CategoryTheory.GrothendieckTopology.OneHypercover

universe u v

variable {C : Type v} [Category.{u} C] {J : GrothendieckTopology C} {X : C}
  {I : Type u} [SmallCategory I] [IsFiltered I]

/-- The presheaf colimit of abelian sheaves satisfies descent for every
finite degree-one hypercover of the site. -/
def filteredColimitIsLimitMultifork (E : J.OneHypercover.{u} X)
    [Finite E.I₀] [Finite E.I₁']
    (F : I ⥤ Sheaf J AddCommGrpCat.{u}) :
    IsLimit (E.multifork
      (colimit (F ⋙ sheafToPresheaf J AddCommGrpCat.{u}))) :=
  E.toPreOneHypercover.filteredColimitIsLimitMultifork
    (F ⋙ sheafToPresheaf J AddCommGrpCat.{u})
    (fun i => E.isLimitMultifork (F.obj i))

end CategoryTheory.GrothendieckTopology.OneHypercover
