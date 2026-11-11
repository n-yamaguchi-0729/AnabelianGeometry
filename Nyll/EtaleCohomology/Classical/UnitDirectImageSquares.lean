/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Descent.FppfGmRepresentable
public import Nyll.EtaleCohomology.Classical.AbelianPushforwardComposition
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Actual unit direct images in arbitrary commuting squares

The maps below pull actual units along actual base-change projections.
They do not require dominance, flatness, or a map of function fields.
Their adjoints therefore apply to Cartier complements under closed graph
maps as well as to dominant morphisms.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

section Over

variable {X U V : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ X)
  (g : V ⟶ U) (h : g ≫ i = j)

/-- The actual base-change map induced by a morphism over the same base. -/
def etaleUnitDirectImageOverSchemeMap (W : X.Etale) :
    pullback W.hom j ⟶ pullback W.hom i :=
  pullback.lift (pullback.fst W.hom j) (pullback.snd W.hom j ≫ g) (by
    rw [Category.assoc, h, pullback.condition])

private theorem unitDirectImageOverSchemeMap_naturality
    {A B : X.Etale} (m : A ⟶ B) :
    ((etaleBaseChange j).map m).left ≫ etaleUnitDirectImageOverSchemeMap i j g h B =
      etaleUnitDirectImageOverSchemeMap i j g h A ≫ ((etaleBaseChange i).map m).left := by
  let a : pullback A.hom j ⟶ pullback B.hom j := ((etaleBaseChange j).map m).left
  let b : pullback A.hom i ⟶ pullback B.hom i := ((etaleBaseChange i).map m).left
  have ha : a ≫ pullback.fst B.hom j = pullback.fst A.hom j ≫ m.left :=
    pullback.lift_fst _ _ _
  have hb : b ≫ pullback.fst B.hom i = pullback.fst A.hom i ≫ m.left :=
    pullback.lift_fst _ _ _
  have ha' : a ≫ pullback.snd B.hom j = pullback.snd A.hom j :=
    pullback.lift_snd _ _ _
  have hb' : b ≫ pullback.snd B.hom i = pullback.snd A.hom i :=
    pullback.lift_snd _ _ _
  change a ≫ etaleUnitDirectImageOverSchemeMap i j g h B =
    etaleUnitDirectImageOverSchemeMap i j g h A ≫ b
  apply pullback.hom_ext
  · have hA : etaleUnitDirectImageOverSchemeMap i j g h A ≫ pullback.fst A.hom i =
        pullback.fst A.hom j := pullback.lift_fst _ _ _
    have hB : etaleUnitDirectImageOverSchemeMap i j g h B ≫ pullback.fst B.hom i =
        pullback.fst B.hom j := pullback.lift_fst _ _ _
    calc
      (a ≫ etaleUnitDirectImageOverSchemeMap i j g h B) ≫ pullback.fst B.hom i =
          a ≫ pullback.fst B.hom j := by rw [Category.assoc, hB]
      _ = pullback.fst A.hom j ≫ m.left := ha
      _ = (etaleUnitDirectImageOverSchemeMap i j g h A ≫ b) ≫ pullback.fst B.hom i := by
        rw [Category.assoc, hb, ← Category.assoc, hA]
  · have hA : etaleUnitDirectImageOverSchemeMap i j g h A ≫ pullback.snd A.hom i =
        pullback.snd A.hom j ≫ g := pullback.lift_snd _ _ _
    have hB : etaleUnitDirectImageOverSchemeMap i j g h B ≫ pullback.snd B.hom i =
        pullback.snd B.hom j ≫ g := pullback.lift_snd _ _ _
    calc
      (a ≫ etaleUnitDirectImageOverSchemeMap i j g h B) ≫ pullback.snd B.hom i =
          pullback.snd A.hom j ≫ g := by
            rw [Category.assoc, hB, ← Category.assoc, ha']
      _ = (etaleUnitDirectImageOverSchemeMap i j g h A ≫ b) ≫ pullback.snd B.hom i := by
        rw [Category.assoc, hb', hA]

/-- Actual direct-image units restrict along any actual morphism over
the base, by its literal map on the base-changed schemes. -/
def etaleUnitDirectImageOverMap :
    (etaleAbelianPushforward i).obj (etaleMultiplicativeGroupSheaf U) ⟶
      (etaleAbelianPushforward j).obj (etaleMultiplicativeGroupSheaf V) :=
  ⟨{ app W := FppfRepresentableGroupSchemeSheaf.GmAbelianSheaf.obj.map
        (etaleUnitDirectImageOverSchemeMap i j g h W.unop).op
     naturality {A B} m := by
       let P : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u} :=
    FppfRepresentableGroupSchemeSheaf.GmAbelianSheaf.obj
       let a : pullback B.unop.hom j ⟶ pullback A.unop.hom j :=
         ((etaleBaseChange j).map m.unop).left
       let b : pullback B.unop.hom i ⟶ pullback A.unop.hom i :=
         ((etaleBaseChange i).map m.unop).left
       change P.map b.op ≫ P.map (etaleUnitDirectImageOverSchemeMap i j g h B.unop).op =
         P.map (etaleUnitDirectImageOverSchemeMap i j g h A.unop).op ≫ P.map a.op
       have hs : a ≫ etaleUnitDirectImageOverSchemeMap i j g h A.unop =
           etaleUnitDirectImageOverSchemeMap i j g h B.unop ≫ b :=
         unitDirectImageOverSchemeMap_naturality i j g h m.unop
       have hn := congrArg
         (fun k : pullback B.unop.hom j ⟶ pullback A.unop.hom i => P.map k.op) hs
       have hleft : P.map b.op ≫
           P.map (etaleUnitDirectImageOverSchemeMap i j g h B.unop).op =
           P.map (etaleUnitDirectImageOverSchemeMap i j g h B.unop ≫ b).op :=
         (P.map_comp b.op (etaleUnitDirectImageOverSchemeMap i j g h B.unop).op).symm
       have hright : P.map (a ≫ etaleUnitDirectImageOverSchemeMap i j g h A.unop).op =
           P.map (etaleUnitDirectImageOverSchemeMap i j g h A.unop).op ≫ P.map a.op :=
         P.map_comp (etaleUnitDirectImageOverSchemeMap i j g h A.unop).op a.op
       exact hleft.trans (hn.symm.trans hright) }⟩

/-- This actual direct-image map retains the original regular units. -/
theorem etaleUnitDirectImageOverMap_unit :
    etaleMultiplicativeGroupToPushforward i ≫ etaleUnitDirectImageOverMap i j g h =
      etaleMultiplicativeGroupToPushforward j := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  let P : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u} :=
    FppfRepresentableGroupSchemeSheaf.GmAbelianSheaf.obj
  let p : pullback W.unop.hom i ⟶ W.unop.left := pullback.fst W.unop.hom i
  let q : pullback W.unop.hom j ⟶ W.unop.left := pullback.fst W.unop.hom j
  let a : pullback W.unop.hom j ⟶ pullback W.unop.hom i :=
    etaleUnitDirectImageOverSchemeMap i j g h W.unop
  have ha : a ≫ p = q := pullback.lift_fst _ _ _
  have he := congrArg
    (fun k : pullback W.unop.hom j ⟶ W.unop.left => P.map k.op) ha
  change P.map p.op ≫ P.map a.op = P.map q.op
  exact (P.map_comp p.op a.op).symm.trans he

end Over

/-- Restriction of original regular units along a composite is the
composite of the two actual direct-image unit maps. -/
theorem etaleMultiplicativeGroupToPushforward_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleMultiplicativeGroupToPushforward (f ≫ g) =
      etaleMultiplicativeGroupToPushforward g ≫
        (etaleAbelianPushforward g).map (etaleMultiplicativeGroupToPushforward f) ≫
          (etaleAbelianPushforwardCompIso f g).hom.app
            (etaleMultiplicativeGroupSheaf X) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  let P : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u} :=
    FppfRepresentableGroupSchemeSheaf.GmAbelianSheaf.obj
  let p : pullback W.unop.hom (f ≫ g) ⟶ W.unop.left :=
    pullback.fst W.unop.hom (f ≫ g)
  let q : pullback W.unop.hom g ⟶ W.unop.left := pullback.fst W.unop.hom g
  let r : pullback (pullback.snd W.unop.hom g) f ⟶ pullback W.unop.hom g :=
    pullback.fst (pullback.snd W.unop.hom g) f
  let m : pullback W.unop.hom (f ≫ g) ⟶
      pullback (pullback.snd W.unop.hom g) f :=
    ((MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) f g).hom.app W.unop).left
  have hc : ((etaleAbelianPushforwardCompIso f g).hom.app
      (etaleMultiplicativeGroupSheaf X)).hom.app (op W.unop) = P.map m.op :=
    etaleAbelianPushforwardCompIso_hom_app f g (etaleMultiplicativeGroupSheaf X) W.unop
  change P.map p.op = P.map q.op ≫ P.map r.op ≫
        ((etaleAbelianPushforwardCompIso f g).hom.app
          (etaleMultiplicativeGroupSheaf X)).hom.app (op W.unop)
  have hp : m ≫ r ≫ q = p :=
    MorphismProperty.Over.pullbackComp_left_fst_fst
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) f g W.unop
  have he := congrArg
    (fun k : pullback W.unop.hom (f ≫ g) ⟶ W.unop.left => P.map k.op) hp
  have hmap : P.map (m ≫ r ≫ q).op = P.map q.op ≫ P.map r.op ≫ P.map m.op :=
    (P.map_comp (r ≫ q).op m.op).trans
      ((congrArg
        (fun k : P.obj (op W.unop.left) ⟶
            P.obj (op (pullback (pullback.snd W.unop.hom g) f)) => k ≫ P.map m.op)
        (P.map_comp q.op r.op)).trans (Category.assoc _ _ _))
  have hcomp : P.map p.op = P.map q.op ≫ P.map r.op ≫ P.map m.op :=
    he.symm.trans hmap
  have htransport := congrArg
    (fun k : P.obj (op (pullback (pullback.snd W.unop.hom g) f)) ⟶
        P.obj (op (pullback W.unop.hom (f ≫ g))) => P.map q.op ≫ P.map r.op ≫ k) hc
  exact hcomp.trans htransport.symm


section Square

variable {X Y U V : Scheme.{u}} (i : U ⟶ X) (f : Y ⟶ X)
  (j : V ⟶ Y) (g : V ⟶ U) (h : g ≫ i = j ≫ f)

/-- The actual map of unit direct images around an arbitrary commuting
square, before taking its inverse-image adjoint. -/
def etaleUnitDirectImageSquareMap :
    (etaleAbelianPushforward i).obj (etaleMultiplicativeGroupSheaf U) ⟶
      (etaleAbelianPushforward f).obj
        ((etaleAbelianPushforward j).obj (etaleMultiplicativeGroupSheaf V)) :=
  etaleUnitDirectImageOverMap i (j ≫ f) g h ≫
    (etaleAbelianPushforwardCompIso j f).inv.app (etaleMultiplicativeGroupSheaf V)

/-- The actual square of regular units and direct-image units commutes. -/
theorem etaleUnitDirectImageSquareMap_unit :
    etaleMultiplicativeGroupToPushforward i ≫
        etaleUnitDirectImageSquareMap i f j g h =
      etaleMultiplicativeGroupToPushforward f ≫
        (etaleAbelianPushforward f).map (etaleMultiplicativeGroupToPushforward j) := by
  let A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := etaleMultiplicativeGroupSheaf X
  let B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (etaleAbelianPushforward f).obj
      ((etaleAbelianPushforward j).obj (etaleMultiplicativeGroupSheaf V))
  let C : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (etaleAbelianPushforward (j ≫ f)).obj (etaleMultiplicativeGroupSheaf V)
  let e : B ≅ C := (etaleAbelianPushforwardCompIso j f).app (etaleMultiplicativeGroupSheaf V)
  let a : A ⟶ B := etaleMultiplicativeGroupToPushforward f ≫
    (etaleAbelianPushforward f).map (etaleMultiplicativeGroupToPushforward j)
  let c : A ⟶ C := etaleMultiplicativeGroupToPushforward (j ≫ f)
  have h0 : etaleMultiplicativeGroupToPushforward i ≫
      etaleUnitDirectImageOverMap i (j ≫ f) g h = c :=
    etaleUnitDirectImageOverMap_unit i (j ≫ f) g h
  have h1 : c = a ≫ e.hom := etaleMultiplicativeGroupToPushforward_comp j f
  change etaleMultiplicativeGroupToPushforward i ≫
    (etaleUnitDirectImageOverMap i (j ≫ f) g h ≫ e.inv) = a
  have h2 : etaleMultiplicativeGroupToPushforward i ≫
      (etaleUnitDirectImageOverMap i (j ≫ f) g h ≫ e.inv) = c ≫ e.inv :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun k : A ⟶ C => k ≫ e.inv) h0)
  have h3 : c ≫ e.inv = a ≫ (e.hom ≫ e.inv) :=
    (congrArg (fun k : A ⟶ C => k ≫ e.inv) h1).trans (Category.assoc _ _ _)
  exact h2.trans
    (h3.trans ((congrArg (fun k : B ⟶ B => a ≫ k) e.hom_inv_id).trans
      (Category.comp_id a)))


/-- The original inverse-image map on direct-image units is adjoint to
the literal square of unit sections. No dominance is required. -/
def etaleUnitDirectImagePullbackSquareMap :
    (etaleAbelianPullback f).obj
        ((etaleAbelianPushforward i).obj (etaleMultiplicativeGroupSheaf U)) ⟶
      (etaleAbelianPushforward j).obj (etaleMultiplicativeGroupSheaf V) :=
  ((etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ _).symm
    (etaleUnitDirectImageSquareMap i f j g h)

/-- The original inverse-image unit map is the left edge of this
constructed square of direct-image unit maps. -/
theorem etaleUnitDirectImagePullbackSquareMap_unit :
    (etaleAbelianPullback f).map (etaleMultiplicativeGroupToPushforward i) ≫
        etaleUnitDirectImagePullbackSquareMap i f j g h =
      etaleMultiplicativeGroupPullback f ≫ etaleMultiplicativeGroupToPushforward j :=
  (etaleAbelianPullbackPushforwardAdjunction f).homEquiv_naturality_right_square
    (etaleMultiplicativeGroupToPushforward i) (etaleUnitDirectImageSquareMap i f j g h)
    (etaleMultiplicativeGroupToPushforward f) (etaleMultiplicativeGroupToPushforward j)
    (etaleUnitDirectImageSquareMap_unit i f j g h)

end Square

end EtaleCohomology
