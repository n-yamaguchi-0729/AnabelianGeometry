/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Sheafification and derived homology

Sheafification compares the homology presheaf of a complex of sheaves with
homology in the abelian category of sheaves.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v u v' u' w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasSheafify J D]

/-- Sheafification identifies the homology presheaf of a complex of sheaves
with its homology in the abelian category of sheaves. -/
def sheafificationPresheafHomologyIso {ι : Type w} (c : ComplexShape ι)
    (K : HomologicalComplex (Sheaf J D) c) (i : ι) :
    (presheafToSheaf J D).obj
      ((((sheafToPresheaf J D).mapHomologicalComplex c).obj K).homology i) ≅
        K.homology i := by
  let A := presheafToSheaf J D
  let P := ((sheafToPresheaf J D).mapHomologicalComplex c).obj K
  let e : sheafToPresheaf J D ⋙ A ≅ 𝟭 (Sheaf J D) :=
    asIso (sheafificationAdjunction J D).counit
  let eK := (Functor.mapHomologicalComplexCompIso e c).app K ≪≫
    (Functor.mapHomologicalComplexIdIso (Sheaf J D) c).app K
  exact ((P.sc i).mapHomologyIso A).symm ≪≫
    (HomologicalComplex.homologyFunctor (Sheaf J D) c i).mapIso eK

variable {B : Type*} [Category B] [Abelian B] [EnoughInjectives B]

/-- A right derived sheaf-valued functor is the sheafification of the homology
presheaf of its value on any injective resolution. -/
def InjectiveResolution.rightDerivedSheafificationIso {X : B}
    (I : InjectiveResolution X) (F : B ⥤ Sheaf J D) [F.Additive] (n : ℕ) :
    (F.rightDerived n).obj X ≅
      (presheafToSheaf J D).obj
        (((((sheafToPresheaf J D).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).homology n)) :=
  I.isoRightDerivedObj F n ≪≫
    (sheafificationPresheafHomologyIso J (ComplexShape.up ℕ)
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) n).symm

end CategoryTheory
