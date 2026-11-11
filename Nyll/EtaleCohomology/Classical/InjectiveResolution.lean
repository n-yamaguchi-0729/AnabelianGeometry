/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.GlobalSectionsComplex
public import Nyll.SchemeTheory.HomologicalAlgebra.ExtInjectiveResolution
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic


/-!
# Classical étale cohomology computed on an injective resolution

A given `InjectiveResolution F` is extended from nonnegative to integer
degrees by the existing zero-extension functor. Its actual augmentation
becomes a quasi-isomorphism from the single complex of `F`, and the
extended resolution is K-injective by mathlib's bounded-below theorem.

The additive derived-Hom and homotopy-Hom comparisons therefore compute
actual small-universe `Sheaf.H` by the Hom complex. The constructed natural
cochain isomorphism then identifies this with the homology of actual global
sections of the extended resolution, followed by the canonical universe lift.
There is no comparison premise or replacement cohomology definition.
-/

@[expose] public section

noncomputable section

universe w v uC u

open AlgebraicGeometry CategoryTheory Limits Opposite
open CochainComplex

namespace EtaleCohomology

/-- Classical `Sheaf.H` is computed by actual global sections of a given
injective resolution, extended by zero to integer degrees. The left-hand
cohomology remains in universe `u`; only the explicit target lift enters the
raw Hom-complex universe. -/
def etaleAbelianCohomologyInjectiveResolutionEquiv
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (I : InjectiveResolution F) (n : ℕ) :
    Sheaf.H.{u} F n ≃+
      (((((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op (⊤_ X.Etale))) ⋙
          AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (I.cocomplex.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) := by
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
  letI : HasDerivedCategory C := HasDerivedCategory.standard C
  let e : Sheaf.H.{u} F n ≃+
      (CochainComplex.HomComplex
        ((CochainComplex.singleFunctor C 0).obj
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u} ℤ))))
        (I.cocomplex.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) :=
    Abelian.extResolutionHomologyEquiv
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) I n
  exact e.trans
    (((HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) (n : ℤ)).mapIso
      ((etaleHomFromIntegerSectionsIso X).app
        (I.cocomplex.extend ComplexShape.embeddingUpNat))).addCommGroupIsoToAddEquiv)

end EtaleCohomology
