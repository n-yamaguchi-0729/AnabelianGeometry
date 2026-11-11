/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Exact transport of injective resolutions

An exact additive functor preserving injective objects transports an actual
injective resolution. The augmentation is transported through the canonical
single-complex isomorphism.
-/

@[expose] public section

noncomputable section

universe u₁ v₁ u₂ v₂

open CategoryTheory

namespace CategoryTheory.InjectiveResolution

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] [F.PreservesInjectiveObjects]

/-- An exact, injective-preserving functor maps an injective resolution to one. -/
def mapExactPreservingInjectives {X : C} (I : InjectiveResolution X) :
    InjectiveResolution (F.obj X) where
  cocomplex := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  injective n := F.injective_obj (I.cocomplex.X n)
  ι := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).inv.app X ≫
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  quasiIso := by infer_instance

end CategoryTheory.InjectiveResolution
