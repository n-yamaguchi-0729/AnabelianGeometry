/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.ConnectedConstants
public import Nyll.EtaleCohomology.Sites.ModuleConstant
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Constant module sheaves on connected schemes

The actual constant-module-sheaf adjunction unit is an isomorphism on a
connected scheme. The underlying constant set sheaf first gives reflection
of isomorphisms. The actual counit comparison and the left triangle identity
then prove invertibility of the unit, hence full faithfulness.

The coefficient ring, module and connected scheme are arbitrary.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable (X : Scheme.{u}) [ConnectedSpace X] (R : Type u) [CommRing R]

/-- The constant module-sheaf functor on a connected scheme reflects isomorphisms. -/
theorem etaleConstantModuleSheaf_reflectsIsomorphisms :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).ReflectsIsomorphisms := by
  have : (constantSheaf X.smallEtaleTopology (Type u)).ReflectsIsomorphisms :=
    (etaleConstantSheafFullyFaithful X).reflectsIsomorphisms
  have : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R) ⋙
      etaleModuleUnderlying X R).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_iso (etaleConstantModuleUnderlyingIso X R).symm
  exact reflectsIsomorphisms_of_comp
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)) (etaleModuleUnderlying X R)

/-- Global sections recover the original module through the actual constant-sheaf
adjunction unit on any connected scheme. -/
theorem etaleConstantModuleSheaf_unit_isIso (M : ModuleCat.{u} R) :
    IsIso ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
      (MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) X)).unit.app M) := by
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let C := constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)
  let adj := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R) hT
  have : (constantSheaf X.smallEtaleTopology (Type u)).Full :=
    (etaleConstantSheafFullyFaithful X).full
  have : (constantSheaf X.smallEtaleTopology (Type u)).Faithful :=
    (etaleConstantSheafFullyFaithful X).faithful
  have : C.ReflectsIsomorphisms := etaleConstantModuleSheaf_reflectsIsomorphisms X R
  have : Sheaf.IsConstant X.smallEtaleTopology
      ((etaleModuleUnderlying X R).obj (C.obj M)) :=
    Sheaf.isConstant_of_iso X.smallEtaleTopology
      ((etaleConstantModuleUnderlyingIso X R).app M)
  have : IsIso (adj.counit.app (C.obj M)) :=
    inferInstanceAs (IsIso (etaleModuleConstantIso X R (C.obj M) hT).hom)
  have : IsIso (C.map (adj.unit.app M)) :=
    isIso_of_comp_hom_eq_id _ (adj.left_triangle_components M)
  exact isIso_of_reflects_iso (adj.unit.app M) C

/-- The constant module-sheaf functor is fully faithful on any connected scheme. -/
def etaleConstantModuleSheafFullyFaithful :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).FullyFaithful := by
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let adj := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R) hT
  have (M : ModuleCat.{u} R) : IsIso (adj.unit.app M) :=
    etaleConstantModuleSheaf_unit_isIso X R M
  have : IsIso adj.unit := NatIso.isIso_of_isIso_app adj.unit
  exact adj.fullyFaithfulLOfIsIsoUnit

end EtaleCohomology
