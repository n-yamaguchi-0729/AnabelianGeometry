/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections

/-!
# Sections of an étale restriction

Identify the top-open sections of a restricted sheaf with its sections on the
corresponding object of the base étale site, compatibly with sheaf morphisms.
-/

@[expose] public section

noncomputable section
universe u v w
open AlgebraicGeometry CategoryTheory Opposite
namespace EtaleCohomology

/-- Postcomposing the terminal Zariski-open object gives the original étale object. -/
noncomputable def etalePostcomposeTopObjectIso
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] :
    (etalePostcompose f).obj ((zariskiToEtale U).obj ⊤) ≅ Scheme.Etale.mk f :=
  (etalePostcompose f).mapIso (zariskiToEtaleTopIso U) ≪≫
    MorphismProperty.Over.isoMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      (Iso.refl U) (by rfl)

/-- Evaluate restriction at the terminal affine-open object without replacing
the actual sheaf by an abstract section module. -/
noncomputable def etaleRestrictionTopObjectSectionIso
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    {A : Type v} [Category.{w} A]
    (F : Sheaf X.smallEtaleTopology A) :
    ((etaleRestriction f A).obj F).obj.obj
      (op ((zariskiToEtale U).obj ⊤)) ≅ F.obj.obj (op (Scheme.Etale.mk f)) :=
  (F.obj.mapIso (asIso (etalePostcomposeTopObjectIso f).hom.op)).symm

/-- The inverse section identification is the actual presheaf restriction map. -/
theorem etaleRestrictionTopObjectSectionIso_inv
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    {A : Type v} [Category.{w} A] (F : Sheaf X.smallEtaleTopology A) :
    (etaleRestrictionTopObjectSectionIso f F).inv =
      F.obj.map (etalePostcomposeTopObjectIso f).hom.op := by
  simp only [etaleRestrictionTopObjectSectionIso, Iso.symm_inv,
    Functor.mapIso_hom, asIso_hom]
  rfl

/-- A restricted sheaf morphism has the original component on the postcomposed object. -/
theorem etaleRestriction_map_hom_app
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    {A : Type v} [Category.{w} A]
    {F G : Sheaf X.smallEtaleTopology A} (a : F ⟶ G) (V : U.Etale) :
    ((etaleRestriction f A).map a).hom.app (op V) =
      a.hom.app (op ((etalePostcompose f).obj V)) := by
  rfl

/-- The object-identification map commutes with every morphism of sheaves. -/
theorem etalePostcomposeTopObjectIso_naturality
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    {A : Type v} [Category.{w} A]
    {F G : Sheaf X.smallEtaleTopology A} (a : F ⟶ G) :
    F.obj.map (etalePostcomposeTopObjectIso f).hom.op ≫
        a.hom.app (op ((etalePostcompose f).obj ((zariskiToEtale U).obj ⊤))) =
      a.hom.app (op (Scheme.Etale.mk f)) ≫
        G.obj.map (etalePostcomposeTopObjectIso f).hom.op :=
  a.hom.naturality (etalePostcomposeTopObjectIso f).hom.op

/-- Transport from an actual object through a sheaf comparison and a comparison
on the restricted site, retaining one categorical section isomorphism. -/
noncomputable def etaleRestrictionComparisonSectionIso
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (e : F ≅ G)
    {H : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}}
    (d : (etaleRestriction f AddCommGrpCat.{u}).obj G ≅ H) :
    F.obj.obj (op (Scheme.Etale.mk f)) ≅
      H.obj.obj (op ((zariskiToEtale U).obj ⊤)) :=
  (etaleRestrictionTopObjectSectionIso f F).symm ≪≫
    (((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u}).mapIso
      ((etaleRestriction f AddCommGrpCat.{u}).mapIso e)).app
        (op ((zariskiToEtale U).obj ⊤))) ≪≫
    (((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u}).mapIso d).app
      (op ((zariskiToEtale U).obj ⊤)))

/-- Its forward map is the actual natural-transformation component, restriction,
and the final comparison component. -/
theorem etaleRestrictionComparisonSectionIso_hom
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (e : F ≅ G)
    {H : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}}
    (d : (etaleRestriction f AddCommGrpCat.{u}).obj G ≅ H) :
    (etaleRestrictionComparisonSectionIso f e d).hom =
      e.hom.hom.app (op (Scheme.Etale.mk f)) ≫
        G.obj.map (etalePostcomposeTopObjectIso f).hom.op ≫
        d.hom.hom.app (op ((zariskiToEtale U).obj ⊤)) := by
  simp only [etaleRestrictionComparisonSectionIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, ObjectProperty.ι_map,
    etaleRestrictionTopObjectSectionIso_inv, etaleRestriction_map_hom_app]
  have hn := etalePostcomposeTopObjectIso_naturality f e.hom
  exact (congrArg (fun m => m ≫ d.hom.hom.app (op ((zariskiToEtale U).obj ⊤))) hn).trans
    (Category.assoc _ _ _)

/-- Convert a section isomorphism using the additive structures of its bundled
objects, before specializing those objects to sheaf sections. -/
def etaleSectionIsoAddEquiv {A B : AddCommGrpCat.{u}} (e : A ≅ B) : A ≃+ B :=
  e.addCommGroupIsoToAddEquiv

/-- The forward section equivalence is the underlying morphism of the isomorphism. -/
theorem etaleSectionIsoAddEquiv_apply
    {A B : AddCommGrpCat.{u}} (e : A ≅ B) (x : A) :
    etaleSectionIsoAddEquiv e x = ConcreteCategory.hom e.hom x := by
  rfl

/-- The inverse section equivalence is the inverse morphism of the isomorphism. -/
theorem etaleSectionIsoAddEquiv_symm_apply
    {A B : AddCommGrpCat.{u}} (e : A ≅ B) (x : B) :
    (etaleSectionIsoAddEquiv e).symm x = ConcreteCategory.hom e.inv x := by
  rfl

/-- The categorical comparison computes its associated additive equivalence. -/
theorem etaleRestrictionComparisonSectionIso_apply
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (e : F ≅ G)
    {H : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}}
    (d : (etaleRestriction f AddCommGrpCat.{u}).obj G ≅ H)
    (x : F.obj.obj (op (Scheme.Etale.mk f))) :
    etaleSectionIsoAddEquiv (etaleRestrictionComparisonSectionIso f e d) x =
      ConcreteCategory.hom (e.hom.hom.app (op (Scheme.Etale.mk f)) ≫
        G.obj.map (etalePostcomposeTopObjectIso f).hom.op ≫
        d.hom.hom.app (op ((zariskiToEtale U).obj ⊤))) x := by
  rw [etaleSectionIsoAddEquiv_apply, etaleRestrictionComparisonSectionIso_hom]

/-- Computing through the single comparison agrees with the three component
additive equivalences, without reconstructing their ambient group structures. -/
theorem etaleRestrictionComparisonSectionIso_addEquiv_apply
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (e : F ≅ G)
    {H : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}}
    (d : (etaleRestriction f AddCommGrpCat.{u}).obj G ≅ H)
    (x : F.obj.obj (op (Scheme.Etale.mk f))) :
    etaleSectionIsoAddEquiv (etaleRestrictionComparisonSectionIso f e d) x =
      ((etaleSectionIsoAddEquiv (etaleRestrictionTopObjectSectionIso f F)).symm.trans
        ((etaleSectionIsoAddEquiv
          (A := ((etaleRestriction f AddCommGrpCat.{u}).obj F).obj.obj
            (op ((zariskiToEtale U).obj ⊤)))
          (B := ((etaleRestriction f AddCommGrpCat.{u}).obj G).obj.obj
            (op ((zariskiToEtale U).obj ⊤)))
          (((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u}).mapIso
            ((etaleRestriction f AddCommGrpCat.{u}).mapIso e)).app
              (op ((zariskiToEtale U).obj ⊤)))).trans
          (etaleSectionIsoAddEquiv
            (A := ((etaleRestriction f AddCommGrpCat.{u}).obj G).obj.obj
              (op ((zariskiToEtale U).obj ⊤)))
            (B := H.obj.obj (op ((zariskiToEtale U).obj ⊤)))
            (((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u}).mapIso d).app
              (op ((zariskiToEtale U).obj ⊤)))))) x := by
  rfl

private theorem etaleSectionAddEquivIsoTransCancel
    {A B C D : AddCommGrpCat.{u}} (e : A ≅ B) (f : A ≃+ C) (g : D ≃+ A) (x : D) :
    ((etaleSectionIsoAddEquiv e).symm.trans f)
      ((g.trans (etaleSectionIsoAddEquiv e)) x) = f (g x) := by
  simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]

/-- The comparison cancels the canonical top-object identification before
applying its two sheaf comparison components. -/
theorem etaleRestrictionComparisonSectionIso_cancel
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (e : F ≅ G)
    {H : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}}
    (d : (etaleRestriction f AddCommGrpCat.{u}).obj G ≅ H)
    {D : AddCommGrpCat.{u}}
    (g : D ≃+ ((etaleRestriction f AddCommGrpCat.{u}).obj F).obj.obj
      (op ((zariskiToEtale U).obj ⊤))) (x : D) :
    (etaleSectionIsoAddEquiv (etaleRestrictionComparisonSectionIso f e d)
      ((g.trans (etaleSectionIsoAddEquiv (etaleRestrictionTopObjectSectionIso f F))) x) :
        H.obj.obj (op ((zariskiToEtale U).obj ⊤))) =
      ((etaleSectionIsoAddEquiv
        (((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u}).mapIso
          ((etaleRestriction f AddCommGrpCat.{u}).mapIso e)).app
            (op ((zariskiToEtale U).obj ⊤)))).trans
        (etaleSectionIsoAddEquiv
          (((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u}).mapIso d).app
            (op ((zariskiToEtale U).obj ⊤))))) (g x) := by
  rw [etaleRestrictionComparisonSectionIso_addEquiv_apply]
  exact etaleSectionAddEquivIsoTransCancel
    (C := H.obj.obj (op ((zariskiToEtale U).obj ⊤))) (D := D)
    (etaleRestrictionTopObjectSectionIso f F) _ g x

/-- Restricting successively along two étale morphisms agrees with restriction
along their composite, using the canonical site composition isomorphism. -/
noncomputable def etaleRestrictionCompIso
    {V U X : Scheme.{u}} (j : V ⟶ U) (i : U ⟶ X)
    [Etale j] [Etale i] (A : Type v) [Category.{w} A] :
    etaleRestriction i A ⋙ etaleRestriction j A ≅
      etaleRestriction (j ≫ i) A :=
  Functor.sheafPushforwardContinuousComp'
    (F := etalePostcompose j) (G := etalePostcompose i)
    (FG := etalePostcompose (j ≫ i))
    (MorphismProperty.Over.mapComp
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      (f := j) inferInstance (g := i) inferInstance).symm
    A V.smallEtaleTopology U.smallEtaleTopology X.smallEtaleTopology

/-- The canonical identification of a terminal restriction object commutes
with the morphism from an étale tower to its intermediate object. -/
theorem etalePostcomposeTopObjectIso_tower
    {V U X : Scheme.{u}} (j : V ⟶ U) (i : U ⟶ X)
    [Etale j] [Etale i] :
    let W := (zariskiToEtale V).obj ⊤
    let t : (etalePostcompose j).obj W ⟶ (zariskiToEtale U).obj ⊤ :=
      (show (etalePostcompose j).obj W ⟶ Scheme.Etale.mk (𝟙 U) from
        MorphismProperty.Over.homMk ((etalePostcompose j).obj W).hom
          (Category.comp_id _)) ≫ (zariskiToEtaleTopIso U).inv
    let m : Scheme.Etale.mk (j ≫ i) ⟶ Scheme.Etale.mk i :=
      MorphismProperty.Over.homMk j rfl
    (MorphismProperty.Over.mapComp
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      (f := j) inferInstance (g := i) inferInstance).hom.app W ≫
        (etalePostcompose i).map t ≫ (etalePostcomposeTopObjectIso i).hom =
      (etalePostcomposeTopObjectIso (j ≫ i)).hom ≫ m := by
  intro W t m
  have hU : (zariskiToEtaleTopIso U).inv.left ≫
      (zariskiToEtaleTopIso U).hom.left = 𝟙 U :=
    congrArg (fun a => a.left) (zariskiToEtaleTopIso U).inv_hom_id
  have hV : (zariskiToEtaleTopIso V).hom.left = W.hom := by
    have hv := MorphismProperty.Over.w (zariskiToEtaleTopIso V).hom
    change (zariskiToEtaleTopIso V).hom.left ≫ 𝟙 V = W.hom at hv
    exact (Category.comp_id _).symm.trans hv
  ext
  change 𝟙 W.left ≫ ((W.hom ≫ j) ≫ (zariskiToEtaleTopIso U).inv.left) ≫
      ((zariskiToEtaleTopIso U).hom.left ≫ 𝟙 U) =
    ((zariskiToEtaleTopIso V).hom.left ≫ 𝟙 V) ≫ j
  have hc {A B C D : Scheme.{u}} (a a' : A ⟶ B) (b : B ⟶ C)
      (s : C ⟶ D) (r : D ⟶ C) (h : s ≫ r = 𝟙 C) (ha : a' = a) :
      𝟙 A ≫ ((a ≫ b) ≫ s) ≫ (r ≫ 𝟙 C) = (a' ≫ 𝟙 B) ≫ b := by
    simp only [Category.id_comp, Category.comp_id, Category.assoc, h, ha]
  exact hc W.hom (zariskiToEtaleTopIso V).hom.left j
    (zariskiToEtaleTopIso U).inv.left (zariskiToEtaleTopIso U).hom.left hU hV

/-- The induced maps on actual sheaf sections respect the same tower. -/
theorem etaleTopObjectSections_tower
    {V U X : Scheme.{u}} (j : V ⟶ U) (i : U ⟶ X)
    [Etale j] [Etale i] {A : Type v} [Category.{w} A]
    (F : Sheaf X.smallEtaleTopology A) :
    let W := (zariskiToEtale V).obj ⊤
    let t : (etalePostcompose j).obj W ⟶ (zariskiToEtale U).obj ⊤ :=
      (show (etalePostcompose j).obj W ⟶ Scheme.Etale.mk (𝟙 U) from
        MorphismProperty.Over.homMk ((etalePostcompose j).obj W).hom
          (Category.comp_id _)) ≫ (zariskiToEtaleTopIso U).inv
    let m : Scheme.Etale.mk (j ≫ i) ⟶ Scheme.Etale.mk i :=
      MorphismProperty.Over.homMk j rfl
    let c := (MorphismProperty.Over.mapComp
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      (f := j) inferInstance (g := i) inferInstance).hom.app W
    F.obj.map m.op ≫ F.obj.map (etalePostcomposeTopObjectIso (j ≫ i)).hom.op =
      F.obj.map (etalePostcomposeTopObjectIso i).hom.op ≫
        F.obj.map ((etalePostcompose i).map t).op ≫ F.obj.map c.op := by
  intro W t m c
  have hm {C : Type (u + 1)} [Category.{u} C] (G : Cᵒᵖ ⥤ A)
      {a b c d e : C} (x : a ⟶ b) (y : b ⟶ c) (z : c ⟶ d)
      (p : a ⟶ e) (q : e ⟶ d) (h : x ≫ y ≫ z = p ≫ q) :
      G.map q.op ≫ G.map p.op = G.map z.op ≫ G.map y.op ≫ G.map x.op := by
    have hh := congrArg (fun f => G.map f.op) h.symm
    simpa only [op_comp, Functor.map_comp, Category.assoc] using hh
  apply hm
  exact etalePostcomposeTopObjectIso_tower j i

/-- A natural transformation transports a compatible composite of section maps. -/
theorem naturality_section_composite
    {C : Type (u + 1)} [Category.{u} C]
    {F G : C ⥤ AddCommGrpCat.{u}} (e : F ⟶ G)
    {X Y : C} (f : X ⟶ Y) {Z W : AddCommGrpCat.{u}}
    (a : G.obj Y ⟶ Z) (b : Z ⟶ W) (v : G.obj X ⟶ W)
    (h : G.map f ≫ a ≫ b = v) :
    F.map f ≫ e.app Y ≫ a ≫ b = e.app X ≫ v := by
  rw [← Category.assoc (F.map f) (e.app Y), e.naturality]
  simpa only [Category.assoc] using congrArg (fun g => e.app X ≫ g) h


end EtaleCohomology
