/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Pointwise direct sums of presheaves

Discrete coproducts of additive-group-valued presheaves are computed
objectwise by direct sums. Every section has finite support in this description.
-/

@[expose] public section

universe u v w

noncomputable section

open CategoryTheory CategoryTheory.Limits DirectSum

namespace AddCommGrpCat

/-- The direct-sum cocone on a discrete family of additive groups. -/
def directSumCocone {ι : Type u} [DecidableEq ι]
    (F : ι → AddCommGrpCat.{u}) : Cocone (Discrete.functor F) where
  pt := AddCommGrpCat.of
    (DirectSum (Discrete ι) (fun i => ((Discrete.functor F).obj i : Type u)))
  ι := Discrete.natTrans fun i =>
    AddCommGrpCat.ofHom
      (DirectSum.of (fun i => ((Discrete.functor F).obj i : Type u)) i)

/-- The direct-sum cocone is colimiting in additive groups. -/
def directSumCoconeIsColimit {ι : Type u} [DecidableEq ι]
    (F : ι → AddCommGrpCat.{u}) : IsColimit (directSumCocone F) where
  desc s := AddCommGrpCat.ofHom <| DirectSum.toAddMonoid
    (fun i => (s.ι.app i).hom)
  fac s i := by
    ext x
    change (DirectSum.toAddMonoid (fun j => (s.ι.app j).hom))
      ((DirectSum.of (fun j => ((Discrete.functor F).obj j : Type u)) i) x) =
      (s.ι.app i).hom x
    rw [DirectSum.toAddMonoid_of]
  uniq s m hm := by
    ext : 1
    apply DirectSum.addHom_ext
    intro i x
    have h := congrArg (fun k => k.hom x) (hm i)
    change m.hom ((DirectSum.of (fun j => ((Discrete.functor F).obj j : Type u)) i) x) =
      (s.ι.app i).hom x at h
    change m.hom ((DirectSum.of (fun j => ((Discrete.functor F).obj j : Type u)) i) x) =
      (DirectSum.toAddMonoid (fun j => (s.ι.app j).hom))
        ((DirectSum.of (fun j => ((Discrete.functor F).obj j : Type u)) i) x)
    rw [DirectSum.toAddMonoid_of]
    exact h

end AddCommGrpCat

namespace Presheaf

variable {C : Type v} [Category.{w, v} C]
variable {ι : Type u} [DecidableEq ι]
variable (F : ι → Cᵒᵖ ⥤ AddCommGrpCat.{u})

/-- The value at an object of the categorical coproduct of additive-group-valued
presheaves is the direct sum of the values of the summands. -/
def discreteCoproductObjIsoDirectSum (U : Cᵒᵖ) :
    (colimit (Discrete.functor F)).obj U ≅
      AddCommGrpCat.of
        (DirectSum (Discrete ι)
          (fun i => (((Discrete.functor F).obj i).obj U : Type u))) := by
  let G := Discrete.functor F
  have e3 : colimit (Discrete.functor
      (fun i => ((evaluation Cᵒᵖ AddCommGrpCat).obj U).obj (F i))) ≅
      AddCommGrpCat.of
        (DirectSum (Discrete ι)
          (fun i => (((Discrete.functor F).obj i).obj U : Type u))) := by
    exact colimit.isoColimitCocone ⟨
      AddCommGrpCat.directSumCocone
        (fun i => ((evaluation Cᵒᵖ AddCommGrpCat).obj U).obj (F i)),
      AddCommGrpCat.directSumCoconeIsColimit
        (fun i => ((evaluation Cᵒᵖ AddCommGrpCat).obj U).obj (F i))⟩
  exact colimitObjIsoColimitCompEvaluation G U ≪≫
    HasColimit.isoOfNatIso
      (Discrete.compNatIsoDiscrete F ((evaluation Cᵒᵖ AddCommGrpCat).obj U)) ≪≫ e3

/-- Every section of a discrete presheaf coproduct is a finite sum of images
of the direct-sum injections, transported back along the pointwise colimit
isomorphism. -/
theorem discreteCoproductObj_eq_finite_sum (U : Cᵒᵖ)
    (s : (colimit (Discrete.functor F)).obj U) :
    ∃ S : Finset (Discrete ι),
      s = ∑ i ∈ S,
        (discreteCoproductObjIsoDirectSum F U).inv.hom
          (DirectSum.of
            (fun j => (((Discrete.functor F).obj j).obj U : Type u)) i
            ((discreteCoproductObjIsoDirectSum F U).hom.hom s i)) := by
  classical
  let e := discreteCoproductObjIsoDirectSum F U
  let d : DirectSum (Discrete ι)
      (fun i => (((Discrete.functor F).obj i).obj U : Type u)) := e.hom.hom s
  refine ⟨d.support, ?_⟩
  have hinv : e.inv.hom (e.hom.hom s) = s := by
    have h := congrArg
      (fun k : (colimit (Discrete.functor F)).obj U ⟶
        (colimit (Discrete.functor F)).obj U => k.hom s) (Iso.hom_inv_id e)
    simpa only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_id,
      AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.id_apply] using h
  have hsum := (DirectSum.sum_support_of d).symm
  calc
    s = e.inv.hom (e.hom.hom s) := hinv.symm
    _ = e.inv.hom d := rfl
    _ = e.inv.hom (∑ i ∈ d.support,
          DirectSum.of
            (fun j => (((Discrete.functor F).obj j).obj U : Type u)) i (d i)) :=
      congrArg e.inv.hom hsum
    _ = ∑ i ∈ d.support,
          e.inv.hom (DirectSum.of
            (fun j => (((Discrete.functor F).obj j).obj U : Type u)) i (d i)) :=
      map_sum _ _ _

/-- The inverse pointwise comparison sends a direct-sum injection to the
corresponding presheaf coproduct injection. -/
theorem discreteCoproductObjIsoDirectSum_inv_of (U : Cᵒᵖ) (i : Discrete ι)
    (x : ((Discrete.functor F).obj i).obj U) :
    (discreteCoproductObjIsoDirectSum F U).inv.hom
      (DirectSum.of
        (fun j => (((Discrete.functor F).obj j).obj U : Type u)) i x) =
      ((colimit.ι (Discrete.functor F) i).app U).hom x := by
  let evalU := (evaluation Cᵒᵖ AddCommGrpCat).obj U
  let H := evalU.obj ∘ F
  let e1 := colimitObjIsoColimitCompEvaluation (Discrete.functor F) U
  let ni := Discrete.compNatIsoDiscrete F evalU
  let e2 := HasColimit.isoOfNatIso ni
  let c3 := AddCommGrpCat.directSumCocone H
  let h3c := AddCommGrpCat.directSumCoconeIsColimit H
  let e3 := colimit.isoColimitCocone ⟨c3, h3c⟩
  let e := discreteCoproductObjIsoDirectSum F U
  have h1 : (colimit.ι (Discrete.functor F) i).app U ≫ e1.hom =
      colimit.ι (Discrete.functor F ⋙ evalU) i :=
    colimitObjIsoColimitCompEvaluation_ι_app_hom (Discrete.functor F) i U
  have h2 : colimit.ι (Discrete.functor F ⋙ evalU) i ≫ e2.hom =
      ni.hom.app i ≫ colimit.ι (Discrete.functor H) i := by
    exact HasColimit.ι_isoOfNatIso_hom ni i
  have h3 : colimit.ι (Discrete.functor H) i ≫ e3.hom = c3.ι.app i :=
    colimit.isoColimitCocone_ι_hom ⟨c3, h3c⟩ i
  have hinv : (colimit.ι (Discrete.functor F) i).app U ≫ e.hom =
      AddCommGrpCat.ofHom (DirectSum.of
        (fun j => (((Discrete.functor F).obj j).obj U : Type u)) i) := by
    change (colimit.ι (Discrete.functor F) i).app U ≫
      (e1.hom ≫ e2.hom ≫ e3.hom) = _
    rw [← Category.assoc, ← Category.assoc, h1, h2, Category.assoc, h3]
    change (𝟙 _) ≫ _ = _
    exact Category.id_comp _
  have h := congrArg (fun k => k.hom x) hinv
  have h' : e.hom.hom (((colimit.ι (Discrete.functor F) i).app U).hom x) =
      DirectSum.of
        (fun j => (((Discrete.functor F).obj j).obj U : Type u)) i x := by
    change e.hom.hom (((colimit.ι (Discrete.functor F) i).app U).hom x) =
      (DirectSum.of
        (fun j => (((Discrete.functor F).obj j).obj U : Type u)) i) x at h
    exact h
  calc
    e.inv.hom (DirectSum.of
        (fun j => (((Discrete.functor F).obj j).obj U : Type u)) i x) =
        e.inv.hom (e.hom.hom (((colimit.ι (Discrete.functor F) i).app U).hom x)) :=
      congrArg e.inv.hom h'.symm
    _ = ((colimit.ι (Discrete.functor F) i).app U).hom x := by
      have hInv (y : (colimit (Discrete.functor F)).obj U) :
          e.inv.hom (e.hom.hom y) = y := by
        have h := congrArg (fun k => k.hom y) (Iso.hom_inv_id e)
        simpa only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_id,
          AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.id_apply] using h
      exact hInv _

end Presheaf
end
