/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectComparison
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectLocalization
public import Nyll.EtaleCohomology.Classical.AbelianRestrictionPullback
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionCohomologySections
public import Nyll.EtaleCohomology.Classical.FreeAbelianCohomologySections
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Sites.EtaleSlice

/-!
# EtaleRestrictionObjectSections

The original degree-zero object restriction, proved on actual coefficient sections.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable {X : Scheme.{u}} {V W : X.Etale} (g : W ⟶ V)

/-- In degree zero the object comparison retains the original
section restriction along the specified morphism of étale objects. -/
theorem etaleCohomologyPresheafRestrictionEquiv_object_restriction_zero
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : Sheaf.H'.{u} F 0 V) :
    etaleCohomologyPresheafRestrictionEquiv W F 0
        ((F.cohomologyPresheaf 0).map g.op a) =
      Sheaf.H.map ((etaleRestrictionObjectIso g).hom.app F) 0
        (etaleAbelianRestrictionCohomologyPullback g.left
          ((etaleRestriction V.hom AddCommGrpCat.{u}).obj F) 0
            (etaleCohomologyPresheafRestrictionEquiv V F 0 a)) := by
  let TV := (etaleSliceEquiv V).functor.obj (Over.mk (𝟙 V))
  let TW := (etaleSliceEquiv W).functor.obj (Over.mk (𝟙 W))
  let hTV : IsTerminal TV := (Over.mkIdTerminal (X := V)).isTerminalObj
    (etaleSliceEquiv V).functor (Over.mk (𝟙 V))
  let hTW : IsTerminal TW := (Over.mkIdTerminal (X := W)).isTerminalObj
    (etaleSliceEquiv W).functor (Over.mk (𝟙 W))
  let cv := (etaleSliceEquiv V).unitIso.app (Over.mk (𝟙 V))
  let cw := (etaleSliceEquiv W).unitIso.app (Over.mk (𝟙 W))
  have hl : g.left ≫ TV.hom = TW.hom ≫ g.left := by
    change g.left ≫ 𝟙 V.left = (𝟙 W.left) ≫ g.left
    rw [Category.comp_id, Category.id_comp]
  let k : (etalePostcompose g.left).obj TW ⟶ TV :=
    MorphismProperty.Over.homMk g.left hl
  have hp := etaleAbelianRestrictionCohomologyPullback_zero_sections
    g.left ((etaleRestriction V.hom AddCommGrpCat.{u}).obj F)
    hTV hTW g.left hl (etaleCohomologyPresheafRestrictionEquiv V F 0 a)
  have hm : etaleRestrictionObjectSiteMap g TW ≫
        (etalePostcompose V.hom).map k ≫ cv.inv.left = cw.inv.left ≫ g := by
    apply MorphismProperty.Over.Hom.ext
    change (𝟙 W.left) ≫ g.left ≫ 𝟙 V.left = (𝟙 W.left) ≫ g.left
    rw [Category.comp_id]
  let I := (etaleRestrictionObjectIso g).hom.app F
  have hright := (Sheaf.H.equiv₀_naturality hTW I
    (etaleAbelianRestrictionCohomologyPullback g.left
      ((etaleRestriction V.hom AddCommGrpCat.{u}).obj F) 0
        (etaleCohomologyPresheafRestrictionEquiv V F 0 a))).symm.trans
    (congrArg (fun z => I.hom.app (op TW) z) hp)
  apply (Sheaf.H.equiv₀ ((etaleRestriction W.hom AddCommGrpCat.{u}).obj F) hTW).injective
  rw [etaleCohomologyPresheafRestrictionEquiv_zero_sections,
    sheafCohomologyPresheaf_zero_sections_map,
    hright,
    etaleCohomologyPresheafRestrictionEquiv_zero_sections,
    etaleRestrictionObjectIso_hom_app]
  let t := freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V F (Ext.addEquiv₀ a)
  change F.obj.map cw.inv.left.op (F.obj.map g.op t) =
    F.obj.map (etaleRestrictionObjectSiteMap g TW).op
      (F.obj.map ((etalePostcompose V.hom).map k).op (F.obj.map cv.inv.left.op t))
  have hmap := congrArg (fun m : (etalePostcompose W.hom).obj TW ⟶ V =>
    F.obj.map m.op) hm
  have hleft : F.obj.map (cw.inv.left ≫ g).op t =
      F.obj.map cw.inv.left.op (F.obj.map g.op t) :=
    ConcreteCategory.congr_hom (F.obj.map_comp g.op cw.inv.left.op) t
  have hright : F.obj.map (etaleRestrictionObjectSiteMap g TW ≫
        (etalePostcompose V.hom).map k ≫ cv.inv.left).op t =
      F.obj.map (etaleRestrictionObjectSiteMap g TW).op
        (F.obj.map ((etalePostcompose V.hom).map k).op (F.obj.map cv.inv.left.op t)) :=
    (ConcreteCategory.congr_hom (F.obj.map_comp
      (((etalePostcompose V.hom).map k) ≫ cv.inv.left).op
      (etaleRestrictionObjectSiteMap g TW).op) t).trans
        (congrArg (fun z => F.obj.map (etaleRestrictionObjectSiteMap g TW).op z)
          (ConcreteCategory.congr_hom (F.obj.map_comp cv.inv.left.op
            ((etalePostcompose V.hom).map k).op) t))
  exact hleft.symm.trans ((ConcreteCategory.congr_hom hmap t).symm.trans hright)

end EtaleCohomology
