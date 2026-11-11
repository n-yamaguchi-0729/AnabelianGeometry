/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.SchemeTheory.Sheaves.OverExtension
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Sections of the original free-abelian cohomology comparisons

The terminal and over-site comparisons were constructed from the same
corepresented evaluation functor. Their actual source isomorphisms
therefore retain the original sections, including the original maps
of the cohomology presheaf. These calculations are used to identify
the source morphisms of the all-degree restriction comparison.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]

/-- The original terminal isomorphism identifies the two actual
corepresenting evaluations, also after any coefficient morphism. -/
theorem freeAbelianSheafYonedaTerminalIso_homEquiv
    {T : C} (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{v})
    (a : (constantSheaf J AddCommGrpCat.{v}).obj
      (AddCommGrpCat.of (ULift.{v} ℤ)) ⟶ F) :
    freeAbelianSheafYonedaHomEquiv J T F
        ((freeAbelianSheafYonedaTerminalIso J hT).hom ≫ a) =
      AddCommGrpCat.uliftZMultiplesAddEquiv _
        ((constantSheafAdj J AddCommGrpCat.{v} hT).homEquiv _ F a) := by
  let Z := (constantSheaf J AddCommGrpCat.{v}).obj
    (AddCommGrpCat.of (ULift.{v} ℤ))
  let e := freeAbelianSheafYonedaHomEquiv J T Z
  have he : e (freeAbelianSheafYonedaTerminalIso J hT).hom =
      AddCommGrpCat.uliftZMultiplesAddEquiv _
        ((constantSheafAdj J AddCommGrpCat.{v} hT).homEquiv _ Z (𝟙 Z)) :=
    e.apply_symm_apply _
  rw [freeAbelianSheafYonedaHomEquiv_postcomp]
  change a.hom.app (op T) (e (freeAbelianSheafYonedaTerminalIso J hT).hom) = _
  let adj := constantSheafAdj J AddCommGrpCat.{v} hT
  have hnat := adj.homEquiv_naturality_right (𝟙 Z) a
  have hid := congrArg (adj.homEquiv (AddCommGrpCat.of (ULift.{v} ℤ)) F)
    (Category.id_comp a)
  exact (congrArg (a.hom.app (op T)) he).trans
    (congrArg (AddCommGrpCat.uliftZMultiplesAddEquiv _)
      (hid.symm.trans hnat)).symm

/-- The inverse of the original over-extension isomorphism preserves
evaluation through its actual two adjunctions. -/
theorem freeAbelianSheafYonedaOverExtensionIso_inv_homEquiv
    (V : C) [HasSheafify (J.over V) AddCommGrpCat.{v}]
    (F : Sheaf J AddCommGrpCat.{v})
    (a : (freeAbelianSheafYoneda J).obj V ⟶ F) :
    AddCommGrpCat.uliftZMultiplesAddEquiv _
        ((constantSheafAdj (J.over V) AddCommGrpCat.{v}
          (Over.mkIdTerminal (X := V))).homEquiv _ (F.over V)
            ((overAbelianSheafExtensionAdjunction V J).homEquiv _ F
              ((freeAbelianSheafYonedaOverExtensionIso J V).inv ≫ a))) =
      freeAbelianSheafYonedaHomEquiv J V F a := by
  let Y := (freeAbelianSheafYoneda J).obj V
  let Z := (constantSheaf (J.over V) AddCommGrpCat.{v}).obj
    (AddCommGrpCat.of (ULift.{v} ℤ))
  let adj := overAbelianSheafExtensionAdjunction V J
  let cAdj := constantSheafAdj (J.over V) AddCommGrpCat.{v}
    (Over.mkIdTerminal (X := V))
  let e : ((overAbelianSheafExtension V J).obj Z ⟶ Y) ≃ Y.obj.obj (op V) :=
    (adj.homEquiv Z Y).trans
      ((cAdj.homEquiv _ (Y.over V)).trans
        (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv)
  have he : e (freeAbelianSheafYonedaOverExtensionIso J V).inv =
      freeAbelianSheafYonedaHomEquiv J V Y (𝟙 Y) :=
    e.apply_symm_apply _
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  change a.hom.app (op V) (e (freeAbelianSheafYonedaOverExtensionIso J V).inv) = _
  exact (congrArg (a.hom.app (op V)) he).trans
    ((freeAbelianSheafYonedaHomEquiv_postcomp J V (𝟙 Y) a).symm.trans
      (congrArg (freeAbelianSheafYonedaHomEquiv J V F) (Category.id_comp a)))

variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- In degree zero the original terminal comparison evaluates to the
original global section. -/
theorem sheafCohomologyTerminalEquiv_zero_sections
    {T : C} (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{v})
    (a : Sheaf.H.{v} F 0) :
    freeAbelianSheafYonedaHomEquiv J T F
        (Ext.addEquiv₀ (sheafCohomologyTerminalEquiv J hT F 0 a)) =
      Sheaf.H.equiv₀ F hT a := by
  have h : Ext.addEquiv₀ (sheafCohomologyTerminalEquiv J hT F 0 a) =
      (freeAbelianSheafYonedaTerminalIso J hT).hom ≫ Ext.addEquiv₀ a := by
    apply (Ext.mk₀_bijective _ F).injective
    change Ext.mk₀ (Ext.addEquiv₀
      ((Ext.mk₀ (freeAbelianSheafYonedaTerminalIso J hT).hom).comp a (zero_add 0))) =
      Ext.mk₀ ((freeAbelianSheafYonedaTerminalIso J hT).hom ≫ Ext.addEquiv₀ a)
    rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
  rw [h]
  exact freeAbelianSheafYonedaTerminalIso_homEquiv J hT F (Ext.addEquiv₀ a)

/-- The original degree-zero cohomology-presheaf restriction is the
original restriction of actual sections. -/
theorem sheafCohomologyPresheaf_zero_sections_map
    {V W : C} (i : V ⟶ W) (F : Sheaf J AddCommGrpCat.{v})
    (a : Sheaf.H'.{v} F 0 W) :
    freeAbelianSheafYonedaHomEquiv J V F
        (Ext.addEquiv₀ ((F.cohomologyPresheaf 0).map i.op a)) =
      F.obj.map i.op (freeAbelianSheafYonedaHomEquiv J W F (Ext.addEquiv₀ a)) := by
  have h : Ext.addEquiv₀ ((F.cohomologyPresheaf 0).map i.op a) =
      (freeAbelianSheafYoneda J).map i ≫ Ext.addEquiv₀ a := by
    apply (Ext.mk₀_bijective _ F).injective
    let a₀ : Ext ((freeAbelianSheafYoneda J).obj W) F 0 := a
    change Ext.mk₀ (Ext.addEquiv₀
      ((Ext.mk₀ ((freeAbelianSheafYoneda J).map i)).comp a₀ (zero_add 0))) =
      Ext.mk₀ ((freeAbelianSheafYoneda J).map i ≫ Ext.addEquiv₀ a₀)
    rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
  rw [h]
  exact freeAbelianSheafYonedaHomEquiv_precomp J i F (Ext.addEquiv₀ a)

/-- The original over-site cohomology comparison retains its actual
degree-zero section, with the canonical terminal object of the slice. -/
theorem sheafCohomologyOverEquiv_zero_sections
    (V : C) [HasBinaryProducts C]
    [HasSheafify (J.over V) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (J.over V) AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (a : Sheaf.H'.{v} F 0 V) :
    Sheaf.H.equiv₀ (F.over V) (Over.mkIdTerminal (X := V))
        (sheafCohomologyOverEquiv J V F 0 a) =
      freeAbelianSheafYonedaHomEquiv J V F (Ext.addEquiv₀ a) := by
  have h : Ext.addEquiv₀ (sheafCohomologyOverEquiv J V F 0 a) =
      (overAbelianSheafExtensionAdjunction V J).homEquiv _ F
        ((freeAbelianSheafYonedaOverExtensionIso J V).inv ≫ Ext.addEquiv₀ a) := by
    apply (Ext.mk₀_bijective _ (F.over V)).injective
    let a₀ : Ext ((freeAbelianSheafYoneda J).obj V) F 0 := a
    change Ext.mk₀ (Ext.addEquiv₀
      ((overAbelianSheafExtensionAdjunction V J).extEquiv
        ((Ext.mk₀ (freeAbelianSheafYonedaOverExtensionIso J V).inv).comp a₀
          (zero_add 0)))) =
      Ext.mk₀ ((overAbelianSheafExtensionAdjunction V J).homEquiv _ F
        ((freeAbelianSheafYonedaOverExtensionIso J V).inv ≫ Ext.addEquiv₀ a₀))
    rw [Ext.mk₀_addEquiv₀_apply, ← Adjunction.extEquiv_mk₀,
      ← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
    ((constantSheafAdj (J.over V) AddCommGrpCat.{v}
      (Over.mkIdTerminal (X := V))).homEquiv _ (F.over V)
        (Ext.addEquiv₀ (sheafCohomologyOverEquiv J V F 0 a))) = _
  rw [h]
  exact freeAbelianSheafYonedaOverExtensionIso_inv_homEquiv J V F (Ext.addEquiv₀ a)

end EtaleCohomology
