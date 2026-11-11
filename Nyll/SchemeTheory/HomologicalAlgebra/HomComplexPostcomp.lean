/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.HomologicalAlgebra.HomFromSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.LeftHomology

/-!
# Actual postcomposition on Hom-complex cohomology

Ordinary postcomposition sends coboundaries to coboundaries. The resulting
map on the existing cohomology classes agrees with both the native homology
map and postcomposition by the shifted map in the homotopy category.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Limits CochainComplex HomComplex

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K L M : CochainComplex C ℤ} (φ : L ⟶ M) (n : ℤ)

/-- Ordinary postcomposition as an additive map of cocycles. -/
def cocyclePostcompAddHom : Cocycle K L n →+ Cocycle K M n where
  toFun z := z.postcomp φ
  map_zero' := by
    apply Subtype.ext
    exact Cochain.zero_comp (Cochain.ofHom φ) (add_zero n)
  map_add' z w := by
    apply Subtype.ext
    exact Cochain.add_comp z.1 w.1 (Cochain.ofHom φ) (add_zero n)

/-- Postcomposition descends to the existing quotient of cocycles by
coboundaries. -/
def cohomologyClassPostcomp : CohomologyClass K L n →+ CohomologyClass K M n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K M n).comp (cocyclePostcompAddHom φ n)) (by
      intro z hz
      change CohomologyClass.mk (z.postcomp φ) = 0
      apply (CohomologyClass.mk_eq_zero_iff (z.postcomp φ)).mpr
      obtain ⟨m, hm, a, ha⟩ := hz
      refine ⟨m, hm, a.comp (Cochain.ofHom φ) (add_zero m), ?_⟩
      rw [HomComplex.δ_comp_ofHom, ha]
      rfl)

theorem cohomologyClassPostcomp_mk (z : Cocycle K L n) :
    cohomologyClassPostcomp φ n (CohomologyClass.mk z) =
      CohomologyClass.mk (z.postcomp φ) := rfl

/-- The original cohomology-class/homotopy-Hom comparison preserves
postcomposition by the given chain map. -/
theorem cohomologyClassPostcomp_toHom (z : CohomologyClass K L n) :
    CohomologyClass.toHom (cohomologyClassPostcomp φ n z) =
      CohomologyClass.toHom z ≫ (HomotopyCategory.quotient C _).map (φ⟦n⟧') := by
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective z
  rw [cohomologyClassPostcomp_mk, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_postcomp, Functor.map_comp, CohomologyClass.toHom_mk]

variable [HasZeroObject C] (A : C)

private def homFromSinglePostcompHomologyData :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n).map
        ((homFromSingleFunctor A).map φ))
      (leftHomologyData ((CochainComplex.singleFunctor C 0).obj A) L n)
      (leftHomologyData ((CochainComplex.singleFunctor C 0).obj A) M n) := by
  let SL : ShortComplex AddCommGrpCat.{v} :=
    (HomComplex ((CochainComplex.singleFunctor C 0).obj A) L).sc n
  let SM : ShortComplex AddCommGrpCat.{v} :=
    (HomComplex ((CochainComplex.singleFunctor C 0).obj A) M).sc n
  let hL : SL.LeftHomologyData :=
    leftHomologyData ((CochainComplex.singleFunctor C 0).obj A) L n
  let hM : SM.LeftHomologyData :=
    leftHomologyData ((CochainComplex.singleFunctor C 0).obj A) M n
  let f : SL ⟶ SM :=
    (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n).map
      ((homFromSingleFunctor A).map φ)
  change ShortComplex.LeftHomologyMapData f hL hM
  let c : hL.K ⟶ hM.K := AddCommGrpCat.ofHom (cocyclePostcompAddHom φ n)
  have hi : c ≫ hM.i = hL.i ≫ f.τ₂ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    rfl
  refine
    { φK := c
      φH := AddCommGrpCat.ofHom (cohomologyClassPostcomp φ n)
      commi := hi
      commf' := ?_
      commπ := ?_ }
  · let d : ShortComplex.LeftHomologyMapData f hL hM := default
    have hc : c = d.φK := (cancel_mono hM.i).mp (hi.trans d.commi.symm)
    exact (congrArg (fun t : hL.K ⟶ hM.K => hL.f' ≫ t) hc).trans d.commf'
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    exact cohomologyClassPostcomp_mk φ n z

/-- The original Hom-complex homology/class comparison preserves the
native homology map of actual postcomposition. -/
theorem homologyAddEquiv_homFromSingle_postcomp
    (z : ((homFromSingleFunctor A).obj L).homology n) :
    homologyAddEquiv ((CochainComplex.singleFunctor C 0).obj A) M n
      (HomologicalComplex.homologyMap ((homFromSingleFunctor A).map φ) n z) =
    cohomologyClassPostcomp φ n
      (homologyAddEquiv ((CochainComplex.singleFunctor C 0).obj A) L n z) :=
  ConcreteCategory.congr_hom
    (homFromSinglePostcompHomologyData φ n A).homologyMap_comm z

end CochainComplex.HomComplex
