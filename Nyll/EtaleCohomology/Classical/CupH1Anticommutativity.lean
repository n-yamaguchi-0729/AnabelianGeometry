/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantCoefficientUnit
public import Nyll.EtaleCohomology.Classical.CupExtensionInterchange
public import Nyll.EtaleCohomology.Classical.CupExtensionRepresentatives
public import Nyll.EtaleCohomology.Classical.CupLocalTensorExactness
public import Nyll.EtaleCohomology.Classical.CupProduct
public import Nyll.EtaleCohomology.Classical.CupTensorAdditive
public import Nyll.EtaleCohomology.Classical.CupTensorSheaves
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Anticommutativity of the original degree-one cup product

Two original Ext classes are represented by actual short extensions
of the constant regular sheaf. Tensoring these extensions forms a
commutative three-by-three diagram. Its actual middle row is short
exact by the proved geometric-stalk tensor exactness; the outer columns
identify with the original extension through the actual unitors.

The native extension-class interchange therefore proves the sign for
the original Yoneda product. The original constant-source comparison
transfers it to the existing étale cup product. Neither a derived
monoidal structure nor a graded-commutativity hypothesis is used.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Abelian MonoidalCategory
open scoped EtaleCohomology.ModuleTensor

namespace EtaleCohomology

section TensorDiagram

variable {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C]

private theorem normalizedTensor_composite_zero {E : C}
    (i : 𝟙_ C ⟶ E) (p : E ⟶ 𝟙_ C) (h : i ≫ p = 0) (A : C) :
    ((λ_ A).inv ≫ (i ▷ A)) ≫ ((p ▷ A) ≫ (λ_ A).hom) = 0 := by
  rw [Category.assoc, ← comp_whiskerRight_assoc, h,
    MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp, Limits.comp_zero]

private def normalizedTensorDiagram {E : C}
    (i : 𝟙_ C ⟶ E) (p : E ⟶ 𝟙_ C) (h : i ≫ p = 0)
    (T : ShortComplex C) : ShortComplex (ShortComplex C) :=
  ShortComplex.mk
    ((T.mapNatIso (leftUnitorNatIso C)).inv ≫
      T.mapNatTrans ((curriedTensor C).map i))
    (T.mapNatTrans ((curriedTensor C).map p) ≫
      (T.mapNatIso (leftUnitorNatIso C)).hom)
    (by
      apply ShortComplex.hom_ext
      · exact normalizedTensor_composite_zero i p h T.X₁
      · exact normalizedTensor_composite_zero i p h T.X₂
      · exact normalizedTensor_composite_zero i p h T.X₃)

private def normalizedTensorColumnIso {E F : C}
    (i : 𝟙_ C ⟶ E) (p : E ⟶ 𝟙_ C) (h : i ≫ p = 0)
    (j : 𝟙_ C ⟶ F) (q : F ⟶ 𝟙_ C) (k : j ≫ q = 0) :
    (normalizedTensorDiagram i p h (ShortComplex.mk j q k)).map ShortComplex.π₁ ≅
      ShortComplex.mk i p h :=
  ShortComplex.isoMk (Iso.refl _) (ρ_ E) (Iso.refl _)
    (by
      change 𝟙 _ ≫ i = ((λ_ (𝟙_ C)).inv ≫ (i ▷ 𝟙_ C)) ≫ (ρ_ E).hom
      simp only [Category.id_comp, Category.assoc, rightUnitor_naturality,
        unitors_inv_equal, Iso.inv_hom_id_assoc])
    (by
      change (ρ_ E).hom ≫ p = ((p ▷ 𝟙_ C) ≫ (λ_ (𝟙_ C)).hom) ≫ 𝟙 _
      rw [Category.comp_id, unitors_equal, rightUnitor_naturality])

end TensorDiagram

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- Actual degree-one extensions of the original constant regular
sheaf anticommute under native Yoneda composition. -/
theorem etaleModuleExt_one_comp_add_eq_zero
    (a b : Ext.{u}
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) 1) :
    a.comp b (show 1 + 1 = 2 from rfl) + b.comp a (show 1 + 1 = 2 from rfl) = 0 := by
  obtain ⟨E, i, p, h, hS, ha⟩ := etaleModuleExt_one_exists_shortExact X R a
  obtain ⟨F, j, q, k, hT, hb⟩ := etaleModuleExt_one_exists_shortExact X R b
  let T := ShortComplex.mk j q k
  let D := normalizedTensorDiagram i p h T
  let e := normalizedTensorColumnIso i p h j q k
  have hL : (D.map ShortComplex.π₁).ShortExact :=
    ShortComplex.shortExact_of_iso e.symm hS
  have hR : (D.map ShortComplex.π₃).ShortExact := hL
  let A := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let cL : Ext.{u} A A 1 := hL.extClass
  let cR : Ext.{u} A A 1 := hR.extClass
  let cT : Ext.{u} A A 1 := hT.extClass
  have hLclass : cL = a := by
    have hc : cL = hS.extClass := by
      have hn := hL.extClass_naturality hS e.hom
      change cL.comp (Ext.mk₀ (𝟙 A)) (add_zero 1) =
        (Ext.mk₀ (𝟙 A)).comp hS.extClass (zero_add 1) at hn
      exact (Ext.comp_mk₀_id cL).symm.trans
        (hn.trans (Ext.mk₀_id_comp hS.extClass))
    exact hc.trans ha
  have hRclass : cR = a := hLclass
  have hTclass : cT = b := hb
  have hmiddle : D.X₂.ShortExact :=
    ModuleTensor.tensorLeft_shortExact_of_unit_quotient X R j q k hT E
  have hsign := CupExtensionInterchange.extClass_comp_add_eq_zero D hT hmiddle hT hL hR
  have hsign' : cR.comp cT rfl + cT.comp cL rfl = 0 := hsign
  simpa only [hLclass, hRclass, hTclass] using hsign'

/-- The two actual original degree-one cup products add to zero, on
every original scheme and for every commutative coefficient ring. -/
theorem etaleCohomologyCup_one_add_swap_eq_zero
    (x y : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) 1) :
    etaleCohomologyCup X R
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
        1 1 2 rfl x y +
      etaleCohomologyCup X R
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
        1 1 2 rfl y x = 0 := by
  rw [etaleCohomologyCup_apply, etaleCohomologyCup_apply, ← map_add,
    etaleModuleExt_one_comp_add_eq_zero, map_zero]

/-- Anticommutativity of the actual original cup product in bidegree
`(1,1)`, proved from actual short extensions and actual tensor exactness. -/
theorem etaleCohomologyCup_anticomm_one
    (x y : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) 1) :
    etaleCohomologyCup X R
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
        1 1 2 rfl x y =
      -etaleCohomologyCup X R
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
        1 1 2 rfl y x :=
  eq_neg_iff_add_eq_zero.mpr (etaleCohomologyCup_one_add_swap_eq_zero X R x y)

end EtaleCohomology
