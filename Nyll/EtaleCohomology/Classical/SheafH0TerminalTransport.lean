/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Original H⁰ sections at different terminal objects

The native degree-zero comparison retains the actual restriction between
terminal objects. This is the naturality of the original morphism from
the constant integer presheaf, before any choice of terminal coordinates.
-/

@[expose] public section

noncomputable section

universe w w'

open CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

/-- Evaluation of an original H⁰ class commutes with the actual map
between any two terminal objects of the site. -/
theorem sheafH0_restriction
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w}) {T T' : C}
    (hT : IsTerminal T) (hT' : IsTerminal T') (i : T ⟶ T')
    (x : Sheaf.H.{w'} F 0) :
    F.obj.map i.op (Sheaf.H.equiv₀ F hT' x) = Sheaf.H.equiv₀ F hT x := by
  let a := Ext.addEquiv₀ x
  let q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{w} ℤ)) ⟶ F.obj :=
    toSheafify J _ ≫ a.hom
  change F.obj.map i.op (q.app (op T') (ULift.up (1 : ℤ))) =
    q.app (op T) (ULift.up (1 : ℤ))
  have h := q.naturality i.op
  simp only [Functor.const_obj_map] at h
  exact (ConcreteCategory.congr_hom h (ULift.up (1 : ℤ))).symm

end EtaleCohomology
