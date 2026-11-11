/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.NatInjectiveResolution
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.SchemeTheory.Sheaves.DerivedHomology
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Sections of the actual higher direct image resolution

The homology presheaf of an actual direct image resolution is evaluated
by cohomology on the corresponding geometric base change.
-/

@[expose] public section

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- The homology presheaf underlying an actual direct image resolution,
evaluated at an étale object, is actual cohomology of the geometric pullback
object. Sheafifying this presheaf computes the higher direct image by
`InjectiveResolution.rightDerivedSheafificationIso`. -/
def etaleDirectImageResolutionSectionEquiv
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (I : InjectiveResolution F) (n : ℕ) :
    ((((sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
      (((etaleAbelianPushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex)).homology n).obj (op V) ≃+
      Sheaf.H'.{u} F n ((etaleBaseChange f).obj V) := by
  let P := ((sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj
      (((etaleAbelianPushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
  let E := (CategoryTheory.evaluation Y.Etaleᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let G := (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (op ((etaleBaseChange f).obj V))
  have : G.Additive :=
    Functor.additive_of_iso
      (sheafSectionsNatIsoEvaluation X.smallEtaleTopology AddCommGrpCat.{u}
        (X := (etaleBaseChange f).obj V)).symm
  let eK : (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj P ≅
      (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex :=
    Iso.refl _
  let e := ((P.sc n).mapHomologyIso E).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).mapIso eK
  exact e.addCommGroupIsoToAddEquiv.trans
    (etaleCohomologyPresheafEvaluationResolutionEquiv X
      ((etaleBaseChange f).obj V) F I n).symm

/-- Objectwise vanishing of actual cohomology on the source site implies
vanishing of the actual higher direct image, using its injective resolution
and exact sheafification. -/
theorem etaleRightDerivedPushforward_isZero_of_cohomologyPresheaf_eq_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (h : ∀ V : X.Etale, ∀ a : Sheaf.H'.{u} F n V, a = 0) :
    IsZero (((etaleAbelianPushforward f).rightDerived n).obj F) := by
  let I := injectiveResolution F
  let G := etaleAbelianPushforward f
  let P := ((sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
  let B := P.homology n
  have hB : IsZero B := by
    apply (IsZero.iff_id_eq_zero B).mpr
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    ext b
    change b = 0
    let e := etaleDirectImageResolutionSectionEquiv f V.unop F I n
    apply e.injective
    rw [e.map_zero]
    exact h ((etaleBaseChange f).obj V.unop) (e b)
  let A := presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}
  exact IsZero.of_iso (A.map_isZero hB)
    (I.rightDerivedSheafificationIso Y.smallEtaleTopology G n)

end EtaleCohomology
