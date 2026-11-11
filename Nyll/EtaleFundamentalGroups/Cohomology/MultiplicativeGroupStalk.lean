/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
public import Nyll.SchemeTheory.Sheaves.UnitStalks
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Nyll.EtaleCohomology.Sites.BaseChange

/-!
# Actual geometric stalks of the multiplicative group and its direct image

Use the single shared filtered-unit comparison for both the original
unit sheaf and its direct image. The latter ring stalk is the filtered
colimit of the actual base-changed rings of sections.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- The actual geometric stalk of Gm is the unit group of the actual
geometric stalk ring, written additively. -/
def geometricMultiplicativeGroupStalkEquiv [IsSepClosed Ω] :
    ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})).obj
      (EtaleCohomology.etaleMultiplicativeGroupSheaf S) ≃+
        Additive (geometricStalk s)ˣ :=
  (Scheme.pointEtaleNeighborhoods s).unitStalkEquiv (etaleSections S)

/-- The actual ring presheaf whose sections are rings of sections on
base changes along the specified scheme morphism. -/
def etaleBaseChangedSections {X : Scheme.{u}} (f : X ⟶ S) :
    S.Etaleᵒᵖ ⥤ CommRingCat.{u} :=
  (EtaleCohomology.etaleBaseChange f).op ⋙ etaleSections X

/-- The geometric stalk of the actual direct image of Gm is the unit
group of the actual base-changed ring stalk. -/
def geometricMultiplicativeGroupPushforwardStalkEquiv [IsSepClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ S) :
    ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})).obj
      ((EtaleCohomology.etaleAbelianPushforward f).obj
        (EtaleCohomology.etaleMultiplicativeGroupSheaf X)) ≃+
      Additive (((Scheme.pointEtaleNeighborhoods s).presheafFiber
        (A := CommRingCat.{u})).obj (etaleBaseChangedSections f))ˣ :=
  (Scheme.pointEtaleNeighborhoods s).unitStalkEquiv (etaleBaseChangedSections f)

/-- The actual map of ring presheaves induced by the base-change
projections, retaining the maps on sections. -/
def etaleSectionsToBaseChanged {X : Scheme.{u}} (f : X ⟶ S) :
    etaleSections S ⟶ etaleBaseChangedSections f where
  app V := (pullback.fst V.unop.hom f).appTop
  naturality {V W} g := by
    have hproj :
        ((EtaleCohomology.etaleBaseChange f).map g.unop).left ≫
          pullback.fst V.unop.hom f =
        pullback.fst W.unop.hom f ≫ g.unop.left := by
      dsimp only [EtaleCohomology.etaleBaseChange]
      exact pullback.lift_fst _ _ _
    change g.unop.left.appTop ≫ (pullback.fst W.unop.hom f).appTop =
      (pullback.fst V.unop.hom f).appTop ≫
        (((EtaleCohomology.etaleBaseChange f).map g.unop).left).appTop
    exact (Scheme.Hom.comp_appTop (pullback.fst W.unop.hom f)
      g.unop.left).symm.trans
        ((congrArg
          (fun k : pullback W.unop.hom f ⟶ V.unop.left => k.appTop)
          hproj.symm).trans
            (Scheme.Hom.comp_appTop
              (((EtaleCohomology.etaleBaseChange f).map g.unop).left)
              (pullback.fst V.unop.hom f)))

/-- The actual direct-image unit map agrees, on geometric stalks, with
the units map induced by the actual ring-stalk homomorphism. -/
theorem geometricMultiplicativeGroupPushforwardStalkEquiv_map
    [IsSepClosed Ω] {X : Scheme.{u}} (f : X ⟶ S)
    (a : ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})).obj
      (EtaleCohomology.etaleMultiplicativeGroupSheaf S)) :
    geometricMultiplicativeGroupPushforwardStalkEquiv s f
      (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})).map
        (EtaleCohomology.etaleMultiplicativeGroupToPushforward f) a) =
      (Units.map
        (((Scheme.pointEtaleNeighborhoods s).presheafFiber (A := CommRingCat.{u})).map
          (etaleSectionsToBaseChanged f)).hom.toMonoidHom).toAdditive
        (geometricMultiplicativeGroupStalkEquiv s a) :=
  (Scheme.pointEtaleNeighborhoods s).unitStalkEquiv_naturality
    (etaleSections S) (etaleSectionsToBaseChanged f) a

/-- Taking an actual geometric stalk of the unit quotient gives the
actual cokernel of the induced map on ring-stalk unit groups. -/
def geometricUnitQuotientStalkIso [IsSepClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ S) :
    ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})).obj
      (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward f)) ≅
    cokernel (AddCommGrpCat.ofHom
      (Units.map
        (((Scheme.pointEtaleNeighborhoods s).presheafFiber
          (A := CommRingCat.{u})).map
            (etaleSectionsToBaseChanged f)).hom.toMonoidHom).toAdditive) := by
  let F := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})
  let g := EtaleCohomology.etaleMultiplicativeGroupToPushforward f
  let e₁ : F.obj (EtaleCohomology.etaleMultiplicativeGroupSheaf S) ≅
      AddCommGrpCat.of (Additive (geometricStalk s)ˣ) :=
    (geometricMultiplicativeGroupStalkEquiv s).toAddCommGrpIso
  let e₂ : F.obj ((EtaleCohomology.etaleAbelianPushforward f).obj
      (EtaleCohomology.etaleMultiplicativeGroupSheaf X)) ≅
      AddCommGrpCat.of
        (Additive (((Scheme.pointEtaleNeighborhoods s).presheafFiber
          (A := CommRingCat.{u})).obj (etaleBaseChangedSections f))ˣ) :=
    (geometricMultiplicativeGroupPushforwardStalkEquiv s f).toAddCommGrpIso
  let p := AddCommGrpCat.ofHom
    (Units.map
      (((Scheme.pointEtaleNeighborhoods s).presheafFiber
        (A := CommRingCat.{u})).map
          (etaleSectionsToBaseChanged f)).hom.toMonoidHom).toAdditive
  have he : F.map g ≫ e₂.hom = e₁.hom ≫ p := by
    apply AddCommGrpCat.ext
    intro a
    exact geometricMultiplicativeGroupPushforwardStalkEquiv_map s f a
  exact PreservesCokernel.iso F g ≪≫
    cokernel.mapIso (f := F.map g) p e₁ e₂ he

end EtaleFundamentalGroups.StrictHenselian
