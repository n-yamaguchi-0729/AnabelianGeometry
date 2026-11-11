/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.HomologicalAlgebra.HomFromSingle
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheaf


/-!
# The constant-integer Hom complex and actual global sections

For a complex `K` of abelian sheaves on the small étale site, the Hom complex
from the constant integer sheaf in degree zero identifies naturally with
the complex obtained by taking actual global sections degreewise.

The raw Hom complex lives in the universe of sheaf morphisms, `u + 1`.
The existing sections remain in `AddCommGrpCat.{u}`; the target uses the
canonical `AddCommGrpCat.uliftFunctor` to express that universe boundary.
No new sheaf-cohomology definition or derived comparison is assumed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open CochainComplex HomComplex

namespace EtaleCohomology

private lemma uliftIntegerHomEquiv_naturality
    {A B : AddCommGrpCat.{u}} (a : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ A) (f : A ⟶ B) :
    AddCommGrpCat.uliftZMultiplesAddEquiv B (a ≫ f) =
      f (AddCommGrpCat.uliftZMultiplesAddEquiv A a) := by
  change (a ≫ f) (ULift.up (1 : ℤ)) = f (a (ULift.up (1 : ℤ)))
  exact CategoryTheory.comp_apply a f (ULift.up (1 : ℤ))

variable (X : Scheme.{u})

local notation "T" => (⊤_ X.Etale)

/-- Maps from the constant integer sheaf are actual global sections. -/
def integerHomSectionsEquiv (F : (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ F) ≃+ F.obj.obj (op T) :=
  ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} terminalIsTerminal).homAddEquiv
    (AddCommGrpCat.of (ULift.{u} ℤ)) F).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)

private lemma integerHomSectionsEquiv_naturality
    {F G : (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})}
    (a : ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ F) (φ : F ⟶ G) :
    integerHomSectionsEquiv X G (a ≫ φ) =
      φ.hom.app (op T) (integerHomSectionsEquiv X F a) := by
  change (AddCommGrpCat.uliftZMultiplesAddEquiv _)
      ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} terminalIsTerminal).homEquiv
        (AddCommGrpCat.of (ULift.{u} ℤ)) G (a ≫ φ)) =
    φ.hom.app (op T) ((AddCommGrpCat.uliftZMultiplesAddEquiv _)
      ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} terminalIsTerminal).homEquiv
        (AddCommGrpCat.of (ULift.{u} ℤ)) F a))
  rw [Adjunction.homEquiv_naturality_right]
  exact uliftIntegerHomEquiv_naturality
    (A := F.obj.obj (op T)) (B := G.obj.obj (op T))
    ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} terminalIsTerminal).homEquiv
      (AddCommGrpCat.of (ULift.{u} ℤ)) F a) (φ.hom.app (op T))

/-- The constant-integer Hom functor identifies naturally with the canonical
universe lift of actual global sections. -/
def etaleIntegerHomSectionsIso :
    preadditiveCoyoneda.obj (op
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))) ≅
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op T)) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  NatIso.ofComponents
    (fun F => ((integerHomSectionsEquiv X F).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (by
      intro F G φ
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro a
      change ULift.up (integerHomSectionsEquiv X G (a ≫ φ)) =
        ULift.up (φ.hom.app (op T) (integerHomSectionsEquiv X F a))
      exact congrArg ULift.up (integerHomSectionsEquiv_naturality X a φ))

/-- The actual Hom complex from the constant integer sheaf in degree zero.
Its maps are ordinary postcomposition of cochains by the given chain map. -/
def etaleHomFromIntegerFunctor :
    CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ ⥤
      CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  homFromSingleFunctor
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))

/-- The natural cochain isomorphism from the raw constant-integer Hom complex
to the canonical universe lift of the existing global-sections complex.
The underlying coefficient sheaves and their section groups remain in universe `u`. -/
def etaleHomFromIntegerSectionsIso :
    etaleHomFromIntegerFunctor X ≅
      (((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op T)) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (ComplexShape.up ℤ) :=
  homFromSingleIso
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) ≪≫
    NatIso.mapHomologicalComplex (etaleIntegerHomSectionsIso X) (ComplexShape.up ℤ)

end EtaleCohomology
