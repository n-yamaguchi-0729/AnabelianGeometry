/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
module

public import Nyll.SchemeTheory.Normalization.FiniteSeparable
public import Nyll.SchemeTheory.FunctionFields.Functoriality
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality

/-! # Matched Generic Arithmetic Coefficient -/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace AnabelianGeometry.WeightFiltration

theorem matchedGeneric_arithmeticFunctionFieldMap_eq
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (hf : DenseRange f)
    (Ω : Type) [Field Ω] [Algebra X.functionField Ω] [Algebra Y.functionField Ω]
    (hpoint : Y.genericExtensionMorphism Ω ≫ f = X.genericExtensionMorphism Ω) :
    (algebraMap Y.functionField Ω).comp (f.functionFieldMap hf) =
      algebraMap X.functionField Ω := by
  have hcat : CommRingCat.ofHom
      ((algebraMap Y.functionField Ω).comp (f.functionFieldMap hf)) =
      CommRingCat.ofHom (algebraMap X.functionField Ω) := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
    change Spec.map (CommRingCat.ofHom (f.functionFieldMap hf) ≫
      CommRingCat.ofHom (algebraMap Y.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X) = X.genericExtensionMorphism Ω
    rw [Spec.map_comp, Category.assoc, EtaleFundamentalGroups.Spec_functionFieldMap_fromSpecStalk,
      ← Category.assoc]
    exact hpoint
  exact congrArg CommRingCat.Hom.hom hcat

theorem matchedGeneric_arithmeticCoordinateMap_eq
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (hf : DenseRange f)
    (Ω : Type) [Field Ω] [Algebra X.functionField Ω] [Algebra Y.functionField Ω]
    {F : Type} [Field F] (e : F ≃+* X.functionField)
    (hpoint : Y.genericExtensionMorphism Ω ≫ f = X.genericExtensionMorphism Ω) :
    ((algebraMap Y.functionField Ω).comp (f.functionFieldMap hf)).comp e.toRingHom =
      (algebraMap X.functionField Ω).comp e.toRingHom :=
  congrArg (fun a : X.functionField →+* Ω => a.comp e.toRingHom)
    (matchedGeneric_arithmeticFunctionFieldMap_eq f hf Ω hpoint)

end AnabelianGeometry.WeightFiltration
