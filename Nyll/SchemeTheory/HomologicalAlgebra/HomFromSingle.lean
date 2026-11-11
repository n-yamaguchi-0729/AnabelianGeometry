/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# The Hom complex from a single object

The original postcomposition construction from the classical global-sections
complex is shared here. The standard `Cochain.fromSingleEquiv` identifies it
naturally with degreewise application of the existing additive coyoneda functor.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Limits Opposite CochainComplex HomComplex

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] (A : C)

/-- The actual Hom complex from the single complex at zero, with ordinary
postcomposition on cochains. -/
def homFromSingleFunctor :
    CochainComplex C ℤ ⥤
      CochainComplex AddCommGrpCat.{v} ℤ where
  obj K := CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj A) K
  map φ :=
    { f := fun n => AddCommGrpCat.ofHom
        { toFun := fun z => z.comp (Cochain.ofHom φ) (add_zero n)
          map_zero' := Cochain.zero_comp _ _
          map_add' := fun z w => Cochain.add_comp z w (Cochain.ofHom φ) (add_zero n) }
      comm' := fun i j _ => by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro z
        exact HomComplex.δ_comp_ofHom z φ j }
  map_id K := by
    apply HomologicalComplex.hom_ext
    intro n
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    exact Cochain.comp_id z
  map_comp φ ψ := by
    apply HomologicalComplex.hom_ext
    intro n
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change z.comp (Cochain.ofHom (φ ≫ ψ)) (add_zero n) =
      (z.comp (Cochain.ofHom φ) (add_zero n)).comp (Cochain.ofHom ψ) (add_zero n)
    rw [Cochain.ofHom_comp]
    exact (Cochain.comp_assoc_of_second_is_zero_cochain z
      (Cochain.ofHom φ) (Cochain.ofHom ψ) (add_zero n)).symm

/-- Identify the Hom complex from a single object with its additive coyoneda complex. -/
def homFromSingleObjIso (K : CochainComplex C ℤ) :
    (homFromSingleFunctor A).obj K ≅
      (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (Cochain.fromSingleEquiv (X := A) (K := K) (zero_add n)).toAddCommGrpIso)
    (by
      intro i j _
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro z
      obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective z i (zero_add i)
      change (Cochain.fromSingleEquiv (zero_add i)
          (Cochain.fromSingleMk a (zero_add i))) ≫ K.d i j =
        Cochain.fromSingleEquiv (zero_add j)
          (HomComplex.δ i j (Cochain.fromSingleMk a (zero_add i)))
      rw [Cochain.δ_fromSingleMk a (zero_add i) j j (zero_add j),
        Cochain.fromSingleEquiv_fromSingleMk, Cochain.fromSingleEquiv_fromSingleMk])

/-- The raw Hom complex from a single object is naturally degreewise additive
coyoneda, through the existing from-single cochain equivalence. -/
def homFromSingleIso :
    homFromSingleFunctor A ≅
      (preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.ofComponents (homFromSingleObjIso A) (by
    intro K L φ
    apply HomologicalComplex.hom_ext
    intro n
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective z n (zero_add n)
    change Cochain.fromSingleEquiv (zero_add n)
        ((Cochain.fromSingleMk a (zero_add n)).comp (Cochain.ofHom φ) (add_zero n)) =
      (Cochain.fromSingleEquiv (zero_add n)
        (Cochain.fromSingleMk a (zero_add n))) ≫ φ.f n
    rw [← Cochain.fromSingleMk_postcomp, Cochain.fromSingleEquiv_fromSingleMk,
      Cochain.fromSingleEquiv_fromSingleMk])

end CategoryTheory
