/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupCechResolution
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCoalgebra
public import Nyll.EtaleCohomology.Classical.FreeModuleYoneda
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The coalgebra counit is the original covering augmentation

The actual free-module counit sends every generator to one. After the
original sheafification it agrees with the existing corepresenting
terminal isomorphism and hence with the original cover augmentation.
Thus the coalgebra action applies to the original Cech resolution,
without a new choice of unit or of augmentation.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Opposite
open scoped EtaleCohomology.ModuleTensor

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- The actual pointwise free-module augmentation. -/
def freeModulePresheafCounit (P : X.Etaleᵒᵖ ⥤ Type u) :
    P ⋙ ModuleCat.free R ⟶ (Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of R R) :=
  ((freeModulePresheafCoalgebra X R).obj P).comon.counit

/-- Every actual free generator has augmentation one. -/
theorem freeModulePresheafCounit_freeMk (P : X.Etaleᵒᵖ ⥤ Type u)
    (V : X.Etaleᵒᵖ) (x : P.obj V) :
    (freeModulePresheafCounit X R P).app V (ModuleCat.freeMk x) = (1 : R) := by
  change Functor.OplaxMonoidal.η (ModuleCat.free R)
      ((ModuleCat.free R).map ((CartesianMonoidalCategory.toUnit P).app V)
        (ModuleCat.freeMk x)) = (1 : R)
  rw [ModuleCat.free_map_apply, ModuleCat.free_η_freeMk]

/-- The original sheafification carries the pointwise augmentation
to the actual coalgebra counit. -/
theorem freeModuleSheafCounit_eq_map (P : X.Etaleᵒᵖ ⥤ Type u) :
    freeModuleSheafCounit X R P =
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
        (freeModulePresheafCounit X R P) := by
  change (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
      (freeModulePresheafCounit X R P) ≫ 𝟙 _ = _
  exact Category.comp_id _

private theorem constantRegularUnit_toSheafify {T : X.Etale} (hT : IsTerminal T) :
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R) hT).unit.app
        (ModuleCat.of R R) =
      (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of R R))).app (op T) := by
  rw [constantSheafAdj, Adjunction.comp_unit_app]
  change 𝟙 (ModuleCat.of R R) ≫ _ = _
  exact Category.id_comp _

/-- Evaluation of the original terminal isomorphism gives the actual
constant section one in the original coefficient sheaf. -/
theorem freeModuleSheafYonedaTerminalIso_hom_sections
    {T : X.Etale} (hT : IsTerminal T) :
    freeModuleSheafYonedaHomEquiv X.smallEtaleTopology R T
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
        (freeModuleSheafYonedaTerminalIso X.smallEtaleTopology R hT).hom =
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R) hT).unit.app
        (ModuleCat.of R R) (1 : R) := by
  let U : Sheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let e := freeModuleSheafYonedaHomEquiv X.smallEtaleTopology R T U
  have he : e (freeModuleSheafYonedaTerminalIso X.smallEtaleTopology R hT).hom =
      ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R) hT).homEquiv
        (ModuleCat.of R R) U (𝟙 U)) (1 : R) :=
    e.apply_symm_apply _
  let adj := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R) hT
  let E := (sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj (op T)
  let η : ModuleCat.of R R ⟶ E.obj U := adj.unit.app (ModuleCat.of R R)
  have hmap : E.map (𝟙 U) = 𝟙 (E.obj U) := E.map_id U
  have hu : adj.homEquiv (ModuleCat.of R R) U (𝟙 U) = η :=
    (congrArg (fun q : E.obj U ⟶ E.obj U => η ≫ q) hmap).trans
      (Category.comp_id η)
  exact he.trans (congrArg (fun q : ModuleCat.of R R ⟶ E.obj U => q (1 : R)) hu)

/-- Evaluation of the actual coalgebra counit gives the same
constant section one, through the original sheafification unit. -/
theorem freeModuleSheafCounit_yoneda_sections (V : X.Etale) :
    freeModuleSheafYonedaHomEquiv X.smallEtaleTopology R V
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
        (freeModuleSheafCounit X R (yoneda.obj V)) =
      (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of R R))).app (op V) (1 : R) := by
  let U : Sheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let q : (freeModuleSheafYoneda X.smallEtaleTopology R).obj V ⟶ U :=
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
      (freeModulePresheafCounit X R (yoneda.obj V))
  calc
    _ = freeModuleSheafYonedaHomEquiv X.smallEtaleTopology R V U q :=
      congrArg (freeModuleSheafYonedaHomEquiv X.smallEtaleTopology R V U)
        (freeModuleSheafCounit_eq_map X R (yoneda.obj V))
    _ = _ := by
      have hη := ConcreteCategory.congr_hom
        (NatTrans.congr_app
          (toSheafify_naturality X.smallEtaleTopology
            (freeModulePresheafCounit X R (yoneda.obj V))) (op V))
        (ModuleCat.freeMk (𝟙 V))
      exact (freeModuleSheafYonedaHomEquiv_apply
        X.smallEtaleTopology R V U q).trans
          (hη.symm.trans
            (congrArg
              ((toSheafify X.smallEtaleTopology
                ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of R R))).app (op V))
              (freeModulePresheafCounit_freeMk X R (yoneda.obj V) (op V) (𝟙 V))))

/-- At the original terminal object the actual coalgebra counit is
exactly the existing corepresenting isomorphism. -/
theorem freeModuleSheafCounit_terminal {T : X.Etale} (hT : IsTerminal T) :
    freeModuleSheafCounit X R (yoneda.obj T) =
      (freeModuleSheafYonedaTerminalIso X.smallEtaleTopology R hT).hom := by
  apply (freeModuleSheafYonedaHomEquiv X.smallEtaleTopology R T
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))).injective
  rw [freeModuleSheafCounit_yoneda_sections,
    freeModuleSheafYonedaTerminalIso_hom_sections, constantRegularUnit_toSheafify]
  rfl

/-- The original cover augmentation is the actual coalgebra counit. -/
theorem freeModuleSheafCounit_eq_moduleCechUnitAugmentation
    {T V : X.Etale} (hT : IsTerminal T) (f : V ⟶ T) :
    freeModuleSheafCounit X R (yoneda.obj V) =
      moduleCechUnitAugmentation X.smallEtaleTopology R hT f := by
  unfold moduleCechUnitAugmentation
  rw [← freeModuleSheafCounit_terminal X R hT]
  exact (freeModuleSheafCounit_naturality X R (yoneda.map f)).symm

end EtaleCohomology
