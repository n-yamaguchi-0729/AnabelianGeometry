/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupCechResolution
public import Nyll.EtaleCohomology.Classical.CupCoefficientSource
public import Nyll.EtaleCohomology.Classical.CupH0Comparison
public import Nyll.EtaleCohomology.Classical.CupProduct
public import Nyll.EtaleCohomology.Classical.FreeAbelianCohomologySections
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafAugmentation
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCochains
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# The actual integer source of the original module Ext comparison

The original cup unit is the degree-zero class of the existing actual
integer-source morphism. On a covering resolution this same morphism
commutes with the actual free abelian to free module source map. The
degree-zero calculation uses the unchanged original units and works
for every terminal representative of the site.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- The original cup unit has the existing actual integer-source
morphism as its degree-zero representative. -/
theorem etaleCohomologyCupUnit_eq_mk₀_constantIntegerHom :
    etaleCohomologyCupUnit X R = Ext.mk₀ (etaleConstantIntegerHom X R) := by
  let C : Sheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let U := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  have hm : (Ext.mk₀ (𝟙 C) : Ext.{u} C C 0).mapExactFunctor U =
      (Ext.mk₀ (𝟙 (U.obj C)) : Ext.{u} (U.obj C) (U.obj C) 0) :=
    (Ext.mapExactFunctor_mk₀ U (𝟙 C)).trans
      (congrArg
        (fun g : U.obj C ⟶ U.obj C => (Ext.mk₀ g : Ext.{u} (U.obj C) (U.obj C) 0))
        (U.map_id C))
  exact (etaleConstantModuleExtCohomologyEquiv_forget X R C 0
    (Ext.mk₀ (𝟙 C))).trans
      ((congrArg
        (fun e : Ext.{u} (U.obj C) (U.obj C) 0 =>
          (Ext.mk₀ (etaleConstantIntegerHom X R)).comp e (zero_add 0)) hm).trans
            (Ext.comp_mk₀_id (Ext.mk₀ (etaleConstantIntegerHom X R))))

/-- Evaluation on a representable keeps the same actual cochain value. -/
theorem freeModuleSheafUnderlyingHomEquiv_yoneda_sections
    (V : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (a : (freeModuleSheafYoneda X.smallEtaleTopology R).obj V ⟶ F) :
    freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V
      ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj F)
        (freeModuleSheafUnderlyingHomEquiv X R (yoneda.obj V) F a) =
      freeModuleSheafYonedaHomEquiv X.smallEtaleTopology R V F a :=
  congrArg (fun η => η.app (op V) (𝟙 V))
    (freeModuleSheafUnderlyingHomEquiv_sections X R (yoneda.obj V) F a)

/-- The original free source comparison at a terminal object has
the same original constant-integer source morphism. -/
theorem freeModuleSheafIntegerMap_terminal
    {T : X.Etale} (hT : IsTerminal T) :
    (freeAbelianSheafYonedaTerminalIso X.smallEtaleTopology hT).hom ≫
        etaleConstantIntegerHom X R =
      freeModuleSheafIntegerMap X R (yoneda.obj T) ≫
        (Classical.forgetCoefficients.{u + 1, u, u, u}).map (freeModuleSheafYonedaTerminalIso
          X.smallEtaleTopology R hT).hom := by
  apply (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology T
    ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)))).injective
  calc
    _ = AddCommGrpCat.uliftZMultiplesAddEquiv _
        ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).homEquiv _ _
          (etaleConstantIntegerHom X R)) :=
      freeAbelianSheafYonedaTerminalIso_homEquiv X.smallEtaleTopology hT
        ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)))
          (etaleConstantIntegerHom X R)
    _ = Sheaf.H.equiv₀ ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))) hT
        (Ext.mk₀ (etaleConstantIntegerHom X R)) := by
      change _ = AddCommGrpCat.uliftZMultiplesAddEquiv _
        ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).homEquiv _ _
          (Ext.addEquiv₀ (Ext.mk₀ (etaleConstantIntegerHom X R))))
      rw [show Ext.addEquiv₀ (Ext.mk₀ (etaleConstantIntegerHom X R)) =
        etaleConstantIntegerHom X R from Ext.addEquiv₀.apply_symm_apply _]
    _ = Sheaf.H.equiv₀ ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))) hT
        (etaleCohomologyCupUnit X R) := by
      rw [etaleCohomologyCupUnit_eq_mk₀_constantIntegerHom]
    _ = freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology T
      ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)))
        (freeModuleSheafUnderlyingHomEquiv X R (yoneda.obj T)
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
          (freeModuleSheafYonedaTerminalIso X.smallEtaleTopology R hT).hom) :=
      (etaleCohomologyCupUnit_sections X R hT).trans
        ((freeModuleSheafYonedaTerminalIso_hom_sections X R hT).symm.trans
          (freeModuleSheafUnderlyingHomEquiv_yoneda_sections X R T
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
              (ModuleCat.of R R)) _).symm)
    _ = _ := by rw [freeModuleSheafUnderlyingHomEquiv_eq]

/-- The original integer and module augmentations form an actual
commuting square with the same generator and constant-source maps. -/
theorem freeModuleSheafIntegerMap_augmentation
    {T : X.Etale} (hT : IsTerminal T) {V : X.Etale} (f : V ⟶ T) :
    abelianCechUnitAugmentation X.smallEtaleTopology hT f ≫ etaleConstantIntegerHom X R =
      freeModuleSheafIntegerMap X R (yoneda.obj V) ≫
        (Classical.forgetCoefficients.{u + 1, u, u, u}).map (moduleCechUnitAugmentation
          X.smallEtaleTopology R hT f) := by
  change ((freeAbelianSheafFunctor X).map (yoneda.map f) ≫
      (freeAbelianSheafYonedaTerminalIso X.smallEtaleTopology hT).hom) ≫
        etaleConstantIntegerHom X R = _
  rw [Category.assoc, freeModuleSheafIntegerMap_terminal, ← Category.assoc,
    freeModuleSheafIntegerMap_naturality, Category.assoc, ← Functor.map_comp]
  rfl

end EtaleCohomology
