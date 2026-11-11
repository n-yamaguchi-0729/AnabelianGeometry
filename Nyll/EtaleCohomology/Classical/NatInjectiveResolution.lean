/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.InjectiveResolution
public import Nyll.SchemeTheory.HomologicalAlgebra.InjectiveResolutionMap
public import Nyll.SchemeTheory.HomologicalAlgebra.MapExtendUpNat
public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Sheaf


/-!
# Classical cohomology and nonnegative injective resolutions

Mapping a zero-extended complex by a zero-preserving functor commutes with
extension: the comparison uses `extendXIso` in nonnegative degrees and
actual zero-object witnesses in negative degrees. This is a constructed
chain isomorphism, not an interchange premise.

The existing extension-homology comparison and exactness of the canonical
abelian-group universe lift then remove the extension and lift from the
classical cohomology calculation. Thus the original small `Sheaf.H` is
computed by actual global sections of the original `ℕ`-indexed resolution.
The existing `InjectiveResolution.isoRightDerivedObj` gives the corresponding
objectwise comparison with `Functor.rightDerived` of actual global sections.
-/

@[expose] public section

noncomputable section

universe uC vC uD vD u

open AlgebraicGeometry CategoryTheory Limits Opposite


namespace EtaleCohomology

/-- Actual global sections commute with zero extension of a nonnegative
complex. The comparison is an explicit chain isomorphism in the original
coefficient universe. -/
def etaleGlobalSectionsExtendIso (X : Scheme.{u})
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℕ) :
    (((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (op (⊤_ X.Etale))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ≅
      ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (op (⊤_ X.Etale))).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
          ComplexShape.embeddingUpNat :=
  Functor.mapExtendUpNatIso
    ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op (⊤_ X.Etale))) K

/-- The original small classical cohomology group is computed by actual global
sections of the original nonnegative injective resolution. Both sides have
carrier universe `u`; extension and universe lift have been explicitly compared
and removed. -/
def etaleAbelianCohomologyNatResolutionEquiv
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (I : InjectiveResolution F) (n : ℕ) :
    Sheaf.H.{u} F n ≃+
      ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (op (⊤_ X.Etale))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex).homology n := by
  let Γ : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op (⊤_ X.Etale))
  let U : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u + 1} := AddCommGrpCat.uliftFunctor.{u + 1, u}
  let K : CochainComplex AddCommGrpCat.{u} ℕ :=
    (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let B : CochainComplex AddCommGrpCat.{u + 1} ℕ :=
    ((Γ ⋙ U).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let eExtend := Functor.mapExtendUpNatIso (Γ ⋙ U) I.cocomplex
  let eComp : (U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ≅ B :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl (Γ ⋙ U)) (ComplexShape.up ℕ)).app I.cocomplex
  let eLift : ((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n ≅
      U.obj (K.homology n) :=
    (K.sc n).mapHomologyIso U
  let e : (((Γ ⋙ U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (I.cocomplex.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) ≅
      U.obj (K.homology n) :=
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) (n : ℤ)).mapIso
        eExtend ≪≫
      B.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) n).mapIso
        eComp.symm ≪≫ eLift
  exact (etaleAbelianCohomologyInjectiveResolutionEquiv X F I n).trans
    (e.addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)

/-- Étale global sections are additive via the canonical sheaf-evaluation
isomorphism and the existing additive inclusion and evaluation functors. -/
instance etaleAbelianGlobalSections_additive (X : Scheme.{u}) :
    ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (op (⊤_ X.Etale))).Additive :=
  Functor.additive_of_iso
    (sheafSectionsNatIsoEvaluation X.smallEtaleTopology AddCommGrpCat.{u}
      (X := ⊤_ X.Etale)).symm

/-- Objectwise identification of actual classical `Sheaf.H` with the existing
right-derived functor of actual abelian global sections. This uses the canonical
supplied injective resolution and its standard derived-functor computation. -/
def etaleAbelianCohomologyRightDerivedEquiv
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u} F n ≃+
      ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (op (⊤_ X.Etale))).rightDerived n).obj F) :=
  (etaleAbelianCohomologyNatResolutionEquiv X F (injectiveResolution F) n).trans
    ((((injectiveResolution F).isoRightDerivedObj
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (op (⊤_ X.Etale))) n).symm).addCommGroupIsoToAddEquiv)

/-- The actual cohomology presheaf can be computed from the original
injective resolution by restriction and actual global sections. -/
def etaleCohomologyPresheafResolutionEquiv
    (X : Scheme.{u}) (V : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (I : InjectiveResolution F) (n : ℕ) :
    Sheaf.H'.{u} F n V ≃+
      ((((etaleRestriction V.hom AddCommGrpCat.{u}) ⋙
        (sheafSections V.left.smallEtaleTopology AddCommGrpCat.{u}).obj
          (op (⊤_ V.left.Etale))).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex).homology n := by
  let R := etaleRestriction V.hom AddCommGrpCat.{u}
  have : R.Additive :=
    inferInstanceAs (etaleRestriction V.hom AddCommGrpCat.{u}).Additive
  let Γ := (sheafSections V.left.smallEtaleTopology AddCommGrpCat.{u}).obj
    (op (⊤_ V.left.Etale))
  let I' := InjectiveResolution.mapExactPreservingInjectives R I
  let eComp := (Functor.mapHomologicalComplexCompIso
    (Iso.refl (R ⋙ Γ)) (ComplexShape.up ℕ)).app I.cocomplex
  let eHom := (HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
    (ComplexShape.up ℕ) n).mapIso eComp
  exact (etaleCohomologyPresheafRestrictionEquiv V F n).trans
    ((etaleAbelianCohomologyNatResolutionEquiv V.left (R.obj F) I' n).trans
      eHom.addCommGroupIsoToAddEquiv)

/-- Global sections after actual étale restriction are sections at the
original étale object. -/
def etaleRestrictionSectionsIso {X : Scheme.{u}} (V : X.Etale) :
    etaleRestriction V.hom AddCommGrpCat.{u} ⋙
      (sheafSections V.left.smallEtaleTopology AddCommGrpCat.{u}).obj
        (op (⊤_ V.left.Etale)) ≅
      (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op V) := by
  let eT : (⊤_ V.left.Etale) ≅ Scheme.Etale.mk (𝟙 V.left) :=
    terminalIsTerminal.uniqueUpToIso
      (MorphismProperty.Over.mkIdTerminal
        (P := show MorphismProperty Scheme.{u} from @Etale) V.left)
  let eId : (etalePostcompose V.hom).obj (Scheme.Etale.mk (𝟙 V.left)) ≅ V :=
    MorphismProperty.Over.isoMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Iso.refl _) (by
      change (𝟙 V.left) ≫ V.hom = (𝟙 V.left) ≫ V.hom
      rfl)
  let e := (etalePostcompose V.hom).mapIso eT ≪≫ eId
  change (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (op ((etalePostcompose V.hom).obj (⊤_ V.left.Etale))) ≅ _
  exact (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).mapIso e.symm.op

/-- Actual cohomology at an étale object is computed by evaluating an
injective resolution of the original sheaf at that object. -/
def etaleCohomologyPresheafEvaluationResolutionEquiv
    (X : Scheme.{u}) (V : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (I : InjectiveResolution F) (n : ℕ) :
    Sheaf.H'.{u} F n V ≃+
      (((((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op V)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).homology n) := by
  have : ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op V)).Additive :=
    Functor.additive_of_iso
      (sheafSectionsNatIsoEvaluation X.smallEtaleTopology AddCommGrpCat.{u}
        (X := V)).symm
  let e := (NatIso.mapHomologicalComplex (etaleRestrictionSectionsIso V)
    (ComplexShape.up ℕ)).app I.cocomplex
  let eh := (HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
    (ComplexShape.up ℕ) n).mapIso e
  exact (etaleCohomologyPresheafResolutionEquiv X V F I n).trans
    eh.addCommGroupIsoToAddEquiv

end EtaleCohomology
