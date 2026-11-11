/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections

/-!
# EtaleRestrictionObjectComparison

The original restriction functors and their actual comparison on coefficient sections.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- Equality of étale morphisms identifies their original restriction functors. -/
def etaleRestrictionCongr
    {U X : Scheme.{u}} {f g : U ⟶ X} [Etale f] [Etale g] (h : f = g) :
    etaleRestriction f AddCommGrpCat.{u} ≅ etaleRestriction g AddCommGrpCat.{u} :=
  eqToIso (by cases h; rfl)

private theorem etaleRestrictionCongr_hom_app
    {U X : Scheme.{u}} {f g : U ⟶ X} [Etale f] [Etale g] (h : f = g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (Z : U.Etale) :
    ((etaleRestrictionCongr h).hom.app F).hom.app (op Z) =
      F.obj.map (MorphismProperty.Over.homMk
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
        (A := (etalePostcompose g).obj Z) (B := (etalePostcompose f).obj Z)
        (𝟙 Z.left) (by
          change (𝟙 Z.left) ≫ (Z.hom ≫ f) = Z.hom ≫ g
          exact (Category.id_comp _).trans
            (congrArg (fun k : U ⟶ X => Z.hom ≫ k) h))).op := by
  cases h
  change 𝟙 _ = F.obj.map (𝟙 (op ((etalePostcompose f).obj Z)))
  exact (F.obj.map_id _).symm

variable {X : Scheme.{u}} {V W : X.Etale} (g : W ⟶ V)

/-- The original composition of restriction functors, with the
original equality supplied by the morphism of étale objects. -/
def etaleRestrictionObjectIso :
    etaleRestriction V.hom AddCommGrpCat.{u} ⋙
        etaleRestriction g.left AddCommGrpCat.{u} ≅
      etaleRestriction W.hom AddCommGrpCat.{u} :=
  etaleRestrictionCompIso g.left V.hom AddCommGrpCat.{u} ≪≫
    etaleRestrictionCongr (show g.left ≫ V.hom = W.hom from g.w)

/-- The actual site arrow comparing restriction along an étale object morphism. -/
def etaleRestrictionObjectSiteMap (Z : W.left.Etale) :
    (etalePostcompose W.hom).obj Z ⟶
      (etalePostcompose V.hom).obj ((etalePostcompose g.left).obj Z) :=
  MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    (𝟙 Z.left) (by
    change (𝟙 Z.left) ≫ ((Z.hom ≫ g.left) ≫ V.hom) = Z.hom ≫ W.hom
    exact (Category.id_comp _).trans ((Category.assoc _ _ _).trans
      (congrArg (fun k : W.left ⟶ X => Z.hom ≫ k)
        (show g.left ≫ V.hom = W.hom from g.w))))

/-- The object comparison acts by the original site arrow on every coefficient section. -/
theorem etaleRestrictionObjectIso_hom_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (Z : W.left.Etale) :
    ((etaleRestrictionObjectIso g).hom.app F).hom.app (op Z) =
      F.obj.map (etaleRestrictionObjectSiteMap g Z).op := by
  let c := (MorphismProperty.Over.mapComp
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    (f := g.left) inferInstance (g := V.hom) inferInstance).app Z
  have hc : ((etaleRestrictionCompIso g.left V.hom AddCommGrpCat.{u}).hom.app F).hom.app
      (op Z) = F.obj.map c.hom.op := by
    change F.obj.map c.hom.op ≫ 𝟙 _ = _
    exact Category.comp_id _
  let d : (etalePostcompose W.hom).obj Z ⟶
      (etalePostcompose (g.left ≫ V.hom)).obj Z :=
    MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      (𝟙 Z.left) (by
        change (𝟙 Z.left) ≫ (Z.hom ≫ (g.left ≫ V.hom)) = Z.hom ≫ W.hom
        exact (Category.id_comp _).trans
          (congrArg (fun k : W.left ⟶ X => Z.hom ≫ k) g.w))
  have hd : ((etaleRestrictionCongr
      (show g.left ≫ V.hom = W.hom from g.w)).hom.app F).hom.app (op Z) =
      F.obj.map d.op := etaleRestrictionCongr_hom_app
        (f := g.left ≫ V.hom) (g := W.hom)
        (show g.left ≫ V.hom = W.hom from g.w) F Z
  have hsite : d ≫ c.hom = etaleRestrictionObjectSiteMap g Z := by
    apply MorphismProperty.Over.Hom.ext
    change (𝟙 Z.left) ≫ (𝟙 Z.left) = 𝟙 Z.left
    exact Category.id_comp _
  change (((etaleRestrictionCompIso g.left V.hom AddCommGrpCat.{u}).hom.app F).hom.app
      (op Z)) ≫ ((etaleRestrictionCongr
        (show g.left ≫ V.hom = W.hom from g.w)).hom.app F).hom.app (op Z) = _
  rw [hc, hd]
  exact (F.obj.map_comp c.hom.op d.op).symm.trans
    (congrArg (fun a : (etalePostcompose W.hom).obj Z ⟶
        (etalePostcompose V.hom).obj ((etalePostcompose g.left).obj Z) =>
      F.obj.map a.op) hsite)

end EtaleCohomology
