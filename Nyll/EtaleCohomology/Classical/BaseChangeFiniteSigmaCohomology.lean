/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.FiniteSigmaCohomology
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.FreeAbelianYonedaPullback
public import Nyll.EtaleCohomology.Constructible.SigmaRepresenter
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Detection on a base-changed finite disjoint union

The original inverse-image functor preserves the coproduct of the
original free abelian representables. Its actual representable
comparison identifies the component maps with actual base change.
Thus restrictions to the base-changed components detect original
cohomology classes, in every degree and for every coefficient sheaf.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (p : X ⟶ Y)
  {ι : Type u} [Finite ι] (U : ι → Y.Etale)
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)

/-- Original restrictions to the base changes of the actual finite
summands jointly detect the original cohomology-presheaf class. -/
theorem etaleBaseChangeFiniteSigmaCohomology_ext
    (a b : Sheaf.H'.{u} F n ((etaleBaseChange p).obj (etaleSigma U)))
    (h : ∀ i, (F.cohomologyPresheaf n).map
        ((etaleBaseChange p).map (etaleSigmaInj U i)).op a =
      (F.cohomologyPresheaf n).map
        ((etaleBaseChange p).map (etaleSigmaInj U i)).op b) : a = b := by
  let : Fintype ι := Fintype.ofFinite ι
  let L := etaleAbelianPullback p
  let P := freeAbelianSheafYoneda Y.smallEtaleTopology
  let Q := freeAbelianSheafYoneda X.smallEtaleTopology
  let B := etaleBaseChange p
  change Ext.{u} (Q.obj (B.obj (etaleSigma U))) F n at a b
  change @Eq (Ext.{u} (Q.obj (B.obj (etaleSigma U))) F n) a b
  let e := freeAbelianSheafYonedaPullbackIso p (etaleSigma U)
  let hC := isColimitCofanMkObjOfIsColimit L (fun i => P.obj (U i))
    (fun i => P.map (etaleSigmaInj U i)) (etaleSigmaFreeAbelianIsColimit U)
  let E := Ext.biproductAddEquiv
    (biconeIsBilimitOfColimitCoconeOfIsColimit hC) F n
  have hn (i : ι) :
      L.map (P.map (etaleSigmaInj U i)) ≫ e.hom =
        (freeAbelianSheafYonedaPullbackIso p (U i)).hom ≫
          Q.map (B.map (etaleSigmaInj U i)) := by
    apply (cancel_epi (freeAbelianSheafYonedaPullbackIso p (U i)).inv).mp
    rw [Iso.inv_hom_id_assoc, ← Category.assoc,
      ← freeAbelianSheafYonedaPullbackIso_inv_naturality,
      Category.assoc, e.inv_hom_id, Category.comp_id]
  have he : (Ext.mk₀ e.hom).comp a (zero_add n) =
      (Ext.mk₀ e.hom).comp b (zero_add n) := by
    apply E.injective
    funext i
    change (Ext.mk₀ (L.map (P.map (etaleSigmaInj U i)))).comp
        ((Ext.mk₀ e.hom).comp a (zero_add n)) (zero_add n) =
      (Ext.mk₀ (L.map (P.map (etaleSigmaInj U i)))).comp
        ((Ext.mk₀ e.hom).comp b (zero_add n)) (zero_add n)
    rw [Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc, hn,
      ← Ext.mk₀_comp_mk₀_assoc, ← Ext.mk₀_comp_mk₀_assoc]
    have hi : (Ext.mk₀ (Q.map (B.map (etaleSigmaInj U i)))).comp a (zero_add n) =
        (Ext.mk₀ (Q.map (B.map (etaleSigmaInj U i)))).comp b (zero_add n) := h i
    exact congrArg (fun z : Ext.{u} (Q.obj (B.obj (U i))) F n =>
      (Ext.mk₀ (freeAbelianSheafYonedaPullbackIso p (U i)).hom).comp z (zero_add n)) hi
  have he' := congrArg (fun z : Ext.{u} (L.obj (P.obj (etaleSigma U))) F n =>
    (Ext.mk₀ e.inv).comp z (zero_add n)) he
  simpa only [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp] using he'

/-- The same detection uses an actual finite disjoint-union
decomposition of the original object, with its unchanged inclusion maps. -/
theorem etaleBaseChangeFiniteSigmaCohomology_ext_of_iso
    {W : Y.Etale} (e : etaleSigma U ≅ W)
    (a b : Sheaf.H'.{u} F n ((etaleBaseChange p).obj W))
    (h : ∀ i, (F.cohomologyPresheaf n).map
        ((etaleBaseChange p).map (etaleSigmaInj U i ≫ e.hom)).op a =
      (F.cohomologyPresheaf n).map
        ((etaleBaseChange p).map (etaleSigmaInj U i ≫ e.hom)).op b) : a = b := by
  let E := (F.cohomologyPresheaf n).mapIso ((etaleBaseChange p).mapIso e).op
  apply E.addCommGroupIsoToAddEquiv.injective
  apply etaleBaseChangeFiniteSigmaCohomology_ext p U F n
  intro i
  change (F.cohomologyPresheaf n).map ((etaleBaseChange p).map (etaleSigmaInj U i)).op
      ((F.cohomologyPresheaf n).map ((etaleBaseChange p).map e.hom).op a) =
    (F.cohomologyPresheaf n).map ((etaleBaseChange p).map (etaleSigmaInj U i)).op
      ((F.cohomologyPresheaf n).map ((etaleBaseChange p).map e.hom).op b)
  simpa only [Functor.map_comp, op_comp, ConcreteCategory.comp_apply] using h i

end EtaleCohomology
