/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionField
import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality

/-!
# The literal generic point of the actual recovered cover

The original generic lift selects the cover-field embedding into Ω. Pulling
that embedding across the inverse of the actual recovery isomorphism gives
exactly the recovered point. No fiber path or conjugating element is chosen.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

universe u

/-- The original cover embedding, transported by the actual recovery inverse,
reconstructs the same point used in the recovered-cover action comparison. -/
theorem recoveredCover_genericExtensionMorphism_eq
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] [Algebra U.functionField Ω]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W)
    {Y : Scheme.{u}} [IsIntegral Y]
    (R : Y ≅ W.left) (x : Spec (.of Ω) ⟶ Y)
    (hxR : x ≫ R.hom =
      (fiberObjEquivHom (U.genericExtensionMorphism Ω) W w).left) :
    letI : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let g := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
    let β := finiteEtaleGenericHomFunctionFieldAlgHom W g
    let hRinv : DenseRange R.inv := R.inv.homeomorph.surjective.denseRange
    let α : Y.functionField →+* Ω :=
      β.toRingHom.comp (R.inv.functionFieldMap hRinv)
    letI : Algebra Y.functionField Ω := α.toAlgebra
    Y.genericExtensionMorphism Ω = x := by
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
  let g := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
  let β := finiteEtaleGenericHomFunctionFieldAlgHom W g
  let hRinv : DenseRange R.inv := R.inv.homeomorph.surjective.denseRange
  let α : Y.functionField →+* Ω :=
    β.toRingHom.comp (R.inv.functionFieldMap hRinv)
  let : Algebra Y.functionField Ω := α.toAlgebra
  have hβ : Spec.map (CommRingCat.ofHom β.toRingHom) ≫
      W.left.fromSpecStalk (genericPoint W.left) = g.left :=
    finiteEtaleGenericHomFunctionFieldAlgHom_spec W g
  have hx : g.left ≫ R.inv = x := by
    rw [← hxR, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change Spec.map (CommRingCat.ofHom α) ≫
    Y.fromSpecStalk (genericPoint Y) = x
  calc
    Spec.map (CommRingCat.ofHom α) ≫ Y.fromSpecStalk (genericPoint Y) =
        Spec.map (CommRingCat.ofHom β.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (R.inv.functionFieldMap hRinv)) ≫
            Y.fromSpecStalk (genericPoint Y) := by
      change Spec.map (CommRingCat.ofHom (R.inv.functionFieldMap hRinv) ≫
        CommRingCat.ofHom β.toRingHom) ≫ _ = _
      rw [Spec.map_comp, Category.assoc]
    _ = Spec.map (CommRingCat.ofHom β.toRingHom) ≫
        W.left.fromSpecStalk (genericPoint W.left) ≫ R.inv := by
      rw [Spec_functionFieldMap_fromSpecStalk R.inv hRinv]
    _ = g.left ≫ R.inv := by rw [← Category.assoc, hβ]
    _ = x := hx

end EtaleFundamentalGroups
