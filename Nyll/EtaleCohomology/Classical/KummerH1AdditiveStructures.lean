/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The canonical additive structures on original Kummer degree-one quotients

The additive parents and commutativity are projections of the existing Ext
additive group. Quotient structures retain that same original owner.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

/-- The original degree-one Ext group, with its existing additive structure. -/
@[instance_reducible]
def kummerFunctorialityH1AddCommGroup (X : Scheme.{u}) :
    AddCommGroup (Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) :=
  inferInstanceAs (AddCommGroup (Abelian.Ext.{u}
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) (etaleMultiplicativeGroupSheaf X) 1))

/-- The additive zero structure inherited from the original degree-one Ext group. -/
@[instance_reducible]
def kummerFunctorialityH1AddZero (X : Scheme.{u}) :
    AddZero (Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) :=
  (kummerFunctorialityH1AddCommGroup X).toAddZeroClass.toAddZero

attribute [local instance] kummerFunctorialityH1AddZero

/-- Addition in the original degree-one Ext group is commutative. -/
theorem kummerFunctorialityH1IsAddCommutative (X : Scheme.{u}) :
    IsAddCommutative (Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) :=
  @AddCommMagma.to_isCommutative _ (kummerFunctorialityH1AddCommGroup X).toAddCommMagma

attribute [local instance] kummerFunctorialityH1IsAddCommutative

/-- The quotient uses the original quotient-group structure's weak additive parent. -/
@[instance_reducible]
def kummerFunctorialityH1QuotientAddZero (X : Scheme.{u}) (n : ℕ) :
    AddZero (Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 ⧸
      (nsmulAddMonoidHom
        (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) n).range) :=
  (@QuotientAddGroup.Quotient.addCommGroup
    (Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) (kummerFunctorialityH1AddCommGroup X)
    (nsmulAddMonoidHom
      (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) n).range).toAddZeroClass.toAddZero

attribute [local instance] kummerFunctorialityH1QuotientAddZero

end EtaleCohomology
