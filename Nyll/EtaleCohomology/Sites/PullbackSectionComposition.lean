/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.PullbackGlobalSectionsComposition
public import Nyll.EtaleCohomology.Sites.PullbackSections
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Composition of inverse-image sections through actual local factors

The chosen inverse-image units and composition isomorphism commute with
the literal local-factor section maps. Native pullback projections identify
the two base-change arrows, and the actual composition-unit equation gives
the section equation. This extends the global-section composition formula
to arbitrary source, intermediate and original étale objects.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

private theorem iterated_pullback_hom_ext
    {A B C D E : Scheme.{u}} (f : A ⟶ C) (g : B ⟶ C) (p : D ⟶ B)
    {k₁ k₂ : E ⟶ pullback (pullback.snd f g) p}
    (hfst : k₁ ≫ pullback.fst (pullback.snd f g) p ≫ pullback.fst f g =
      k₂ ≫ pullback.fst (pullback.snd f g) p ≫ pullback.fst f g)
    (hsnd : k₁ ≫ pullback.snd (pullback.snd f g) p =
      k₂ ≫ pullback.snd (pullback.snd f g) p) : k₁ = k₂ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using hfst
    · calc
        (k₁ ≫ pullback.fst (pullback.snd f g) p) ≫ pullback.snd f g =
            k₁ ≫ pullback.snd (pullback.snd f g) p ≫ p := by
          rw [Category.assoc, pullback.condition]
        _ = k₂ ≫ pullback.snd (pullback.snd f g) p ≫ p := by
          rw [← Category.assoc, hsnd, Category.assoc]
        _ = (k₂ ≫ pullback.fst (pullback.snd f g) p) ≫ pullback.snd f g := by
          rw [Category.assoc, pullback.condition]
  · exact hsnd

variable {X Y Z : Scheme.{u}} (p : Z ⟶ Y) (q : Y ⟶ X)

/-- Native base-change arrows associated to two local factors compose
through the canonical comparison of the base-change functors. -/
theorem etaleBaseChangeLift_composition
    {U : Z.Etale} {V : Y.Etale} {W : X.Etale}
    (l : U.left ⟶ V.left) (hl : l ≫ V.hom = U.hom ≫ p)
    (m : V.left ⟶ W.left) (hm : m ≫ W.hom = V.hom ≫ q)
    (hcomp : (l ≫ m) ≫ W.hom = U.hom ≫ (p ≫ q)) :
    etaleBaseChangeLift (p ≫ q) (l ≫ m) hcomp ≫
        (MorphismProperty.Over.pullbackComp
          (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) p q).hom.app W =
      etaleBaseChangeLift p l hl ≫ (etaleBaseChange p).map (etaleBaseChangeLift q m hm) := by
  let Wq := (etaleBaseChange q).obj W
  let Wp := (etaleBaseChange p).obj V
  let Wc := (etaleBaseChange (p ≫ q)).obj W
  let Wpq := (etaleBaseChange p).obj Wq
  let aq : V ⟶ Wq := etaleBaseChangeLift q m hm
  let ap : U ⟶ Wp := etaleBaseChangeLift p l hl
  let ac : U ⟶ Wc := etaleBaseChangeLift (p ≫ q) (l ≫ m) hcomp
  let c : Wc ⟶ Wpq := (MorphismProperty.Over.pullbackComp
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) p q).hom.app W
  let d : Wp ⟶ Wpq := (etaleBaseChange p).map aq
  have hcfst : c.left ≫ pullback.fst Wq.hom p ≫ pullback.fst W.hom q =
      pullback.fst W.hom (p ≫ q) :=
    MorphismProperty.Over.pullbackComp_left_fst_fst
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) p q W
  have hdfst : d.left ≫ pullback.fst Wq.hom p = pullback.fst V.hom p ≫ aq.left :=
    pullback.lift_fst _ _ _
  have haq : aq.left ≫ pullback.fst W.hom q = m := pullback.lift_fst _ _ _
  have hap : ap.left ≫ pullback.fst V.hom p = l := pullback.lift_fst _ _ _
  have hac : ac.left ≫ pullback.fst W.hom (p ≫ q) = l ≫ m := pullback.lift_fst _ _ _
  have hleft : (ac ≫ c).left ≫ pullback.fst Wq.hom p ≫ pullback.fst W.hom q = l ≫ m := by
    change (ac.left ≫ c.left) ≫ _ ≫ _ = _
    rw [Category.assoc, hcfst, hac]
  have hright : (ap ≫ d).left ≫ pullback.fst Wq.hom p ≫ pullback.fst W.hom q = l ≫ m := by
    change (ap.left ≫ d.left) ≫ _ ≫ _ = _
    have hd : d.left ≫ pullback.fst Wq.hom p ≫ pullback.fst W.hom q =
        pullback.fst V.hom p ≫ m :=
      (Category.assoc d.left (pullback.fst Wq.hom p) (pullback.fst W.hom q)).symm.trans
        ((congrArg (fun a => a ≫ pullback.fst W.hom q) hdfst).trans
          ((Category.assoc (pullback.fst V.hom p) aq.left (pullback.fst W.hom q)).trans
            (congrArg (fun a => pullback.fst V.hom p ≫ a) haq)))
    exact (Category.assoc ap.left d.left
      (pullback.fst Wq.hom p ≫ pullback.fst W.hom q)).trans
      ((congrArg (fun a => ap.left ≫ a) hd).trans
        ((Category.assoc ap.left (pullback.fst V.hom p) m).symm.trans
          (congrArg (fun a => a ≫ m) hap)))
  change ac ≫ c = ap ≫ d
  apply MorphismProperty.Over.Hom.ext
  apply iterated_pullback_hom_ext W.hom q p
  · exact hleft.trans hright.symm
  · exact (ac ≫ c).w.trans (ap ≫ d).w.symm

variable (Λ : Type u) [CommRing Λ]

/-- Pulling through successive local factors equals pulling through their
composite, under the actual inverse-image composition isomorphism. -/
theorem etalePullbackSectionMap_comp
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {U : Z.Etale} {V : Y.Etale} {W : X.Etale}
    (l : U.left ⟶ V.left) (hl : l ≫ V.hom = U.hom ≫ p)
    (m : V.left ⟶ W.left) (hm : m ≫ W.hom = V.hom ≫ q)
    (hcomp : (l ≫ m) ≫ W.hom = U.hom ≫ (p ≫ q)) :
    etalePullbackSectionMap (p ≫ q) Λ F (l ≫ m) hcomp ≫
        ((etalePullbackCompIso p q Λ).hom.app F).hom.app (op U) =
      etalePullbackSectionMap q Λ F m hm ≫
        etalePullbackSectionMap p Λ ((etalePullback q Λ).obj F) l hl := by
  let Wq : Y.Etale := (etaleBaseChange q).obj W
  let Wp : Z.Etale := (etaleBaseChange p).obj V
  let Wc : Z.Etale := (etaleBaseChange (p ≫ q)).obj W
  let Wpq : Z.Etale := (etaleBaseChange p).obj Wq
  let aq : V ⟶ Wq := etaleBaseChangeLift q m hm
  let ap : U ⟶ Wp := etaleBaseChangeLift p l hl
  let ac : U ⟶ Wc := etaleBaseChangeLift (p ≫ q) (l ≫ m) hcomp
  let c : Wc ⟶ Wpq :=
    (MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) p q).hom.app W
  let d : Wp ⟶ Wpq := (etaleBaseChange p).map aq
  have hac : ac ≫ c = ap ≫ d := etaleBaseChangeLift_composition p q l hl m hm hcomp
  let Fq := (etalePullback q Λ).obj F
  let Fc := (etalePullback (p ≫ q) Λ).obj F
  let Fpq := (etalePullback p Λ).obj Fq
  let A := F.obj.obj (op W)
  let Pq : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ := Fq.obj
  let Pc : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ := Fc.obj
  let Ppq : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ := Fpq.obj
  let e : Pc ⟶ Ppq := ((etalePullbackCompIso p q Λ).hom.app F).hom
  let uq : A ⟶ Pq.obj (op Wq) :=
    ((etalePullbackPushforwardAdjunction q Λ).unit.app F).hom.app (op W)
  let uc : A ⟶ Pc.obj (op Wc) :=
    ((etalePullbackPushforwardAdjunction (p ≫ q) Λ).unit.app F).hom.app (op W)
  let up : Pq.obj (op V) ⟶ Ppq.obj (op Wp) :=
    ((etalePullbackPushforwardAdjunction p Λ).unit.app Fq).hom.app (op V)
  let upq : Pq.obj (op Wq) ⟶ Ppq.obj (op Wpq) :=
    ((etalePullbackPushforwardAdjunction p Λ).unit.app Fq).hom.app (op Wq)
  let rq : Pq.obj (op Wq) ⟶ Pq.obj (op V) := Pq.map aq.op
  let rp : Ppq.obj (op Wp) ⟶ Ppq.obj (op U) := Ppq.map ap.op
  let rc : Pc.obj (op Wc) ⟶ Pc.obj (op U) := Pc.map ac.op
  let rcpq : Ppq.obj (op Wc) ⟶ Ppq.obj (op U) := Ppq.map ac.op
  let hc : Ppq.obj (op Wpq) ⟶ Ppq.obj (op Wc) := Ppq.map c.op
  let hd : Ppq.obj (op Wpq) ⟶ Ppq.obj (op Wp) := Ppq.map d.op
  let ec : Pc.obj (op Wc) ⟶ Ppq.obj (op Wc) := e.app (op Wc)
  let e₀ : Pc.obj (op U) ⟶ Ppq.obj (op U) := e.app (op U)
  have he : rc ≫ e₀ = ec ≫ rcpq := e.naturality ac.op
  have hp : rq ≫ up = upq ≫ hd :=
    ((etalePullbackPushforwardAdjunction p Λ).unit.app Fq).hom.naturality aq.op
  have hmap : hc ≫ rcpq = hd ≫ rp := by
    calc
      hc ≫ rcpq = Ppq.map (ac ≫ c).op := (Ppq.map_comp c.op ac.op).symm
      _ = Ppq.map (ap ≫ d).op := congrArg (fun k : U ⟶ Wpq => Ppq.map k.op) hac
      _ = hd ≫ rp := Ppq.map_comp d.op ap.op
  have hu : uc ≫ ec = (uq ≫ upq) ≫ hc := by
    have h := congrArg
      (fun k : F ⟶ (etalePushforward (p ≫ q) Λ).obj Fpq => k.hom.app (op W))
      (etalePullbackComp_unit p q Λ F)
    change uc ≫ ec = (uq ≫ upq) ≫ (𝟙 _ ≫ hc) at h
    exact h.trans (congrArg (fun k => (uq ≫ upq) ≫ k) (Category.id_comp hc))
  change (uc ≫ rc) ≫ e₀ = (uq ≫ rq) ≫ (up ≫ rp)
  calc
    (uc ≫ rc) ≫ e₀ = (uc ≫ ec) ≫ rcpq := by
      rw [Category.assoc, he, ← Category.assoc]
    _ = (uq ≫ upq) ≫ (hc ≫ rcpq) := by rw [hu, Category.assoc]
    _ = (uq ≫ upq) ≫ (hd ≫ rp) := congrArg (fun k => (uq ≫ upq) ≫ k) hmap
    _ = (uq ≫ (upq ≫ hd)) ≫ rp := by simp only [Category.assoc]
    _ = (uq ≫ (rq ≫ up)) ≫ rp := by rw [← hp]
    _ = (uq ≫ rq) ≫ (up ≫ rp) := by simp only [Category.assoc]


/-- Transport of the base morphism preserves the literal local-factor
section map through the canonical equality isomorphism of inverse images. -/
theorem etalePullbackSectionMap_congr
    {q' : Y ⟶ X} (h : q = q')
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {U : Y.Etale} {V : X.Etale}
    (l : U.left ⟶ V.left)
    (hl : l ≫ V.hom = U.hom ≫ q) (hl' : l ≫ V.hom = U.hom ≫ q') :
    etalePullbackSectionMap q Λ F l hl ≫
        ((eqToIso (congrArg (fun r => etalePullback r Λ) h)).hom.app F).hom.app (op U) =
      etalePullbackSectionMap q' Λ F l hl' := by
  cases h
  change etalePullbackSectionMap q Λ F l hl ≫ 𝟙 _ = etalePullbackSectionMap q Λ F l hl
  exact Category.comp_id _

/-- Successive local-factor pullbacks transported along the actual
composition and base-morphism equality isomorphisms give the pullback
through the specified composite factor. -/
theorem etalePullbackSectionMap_comp_congr
    (r : Z ⟶ X) (h : p ≫ q = r)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {U : Z.Etale} {V : Y.Etale} {W : X.Etale}
    (l : U.left ⟶ V.left) (hl : l ≫ V.hom = U.hom ≫ p)
    (m : V.left ⟶ W.left) (hm : m ≫ W.hom = V.hom ≫ q)
    (n : U.left ⟶ W.left) (hn : n ≫ W.hom = U.hom ≫ r) (hln : l ≫ m = n) :
    etalePullbackSectionMap q Λ F m hm ≫
      etalePullbackSectionMap p Λ ((etalePullback q Λ).obj F) l hl ≫
      ((((etalePullbackCompIso p q Λ).symm ≪≫
        eqToIso (congrArg (fun k => etalePullback k Λ) h)).hom.app F).hom.app (op U)) =
    etalePullbackSectionMap r Λ F n hn := by
  subst n
  have hc : (l ≫ m) ≫ W.hom = U.hom ≫ (p ≫ q) :=
    (Category.assoc l m W.hom).trans
      ((congrArg (fun a => l ≫ a) hm).trans
        ((Category.assoc l V.hom q).symm.trans
          ((congrArg (fun a => a ≫ q) hl).trans (Category.assoc U.hom p q))))
  let e := ((sheafSections Z.smallEtaleTopology (ModuleCat.{u} Λ)).obj (op U)).mapIso
    ((etalePullbackCompIso p q Λ).app F)
  let j := ((sheafSections Z.smallEtaleTopology (ModuleCat.{u} Λ)).obj (op U)).mapIso
    ((eqToIso (congrArg (fun k => etalePullback k Λ) h)).app F)
  let a := etalePullbackSectionMap q Λ F m hm
  let b := etalePullbackSectionMap p Λ ((etalePullback q Λ).obj F) l hl
  let c := etalePullbackSectionMap (p ≫ q) Λ F (l ≫ m) hc
  have he : c ≫ e.hom = a ≫ b := etalePullbackSectionMap_comp p q Λ F l hl m hm hc
  have hj : c ≫ j.hom = etalePullbackSectionMap r Λ F (l ≫ m) hn :=
    etalePullbackSectionMap_congr (p ≫ q) Λ h F (l ≫ m) hc hn
  change a ≫ b ≫ (e.inv ≫ j.hom) = _
  exact (Category.assoc a b (e.inv ≫ j.hom)).symm.trans
    ((congrArg (fun k => k ≫ (e.inv ≫ j.hom)) he.symm).trans
      ((Category.assoc c e.hom (e.inv ≫ j.hom)).trans
        ((congrArg (fun k => c ≫ k)
          ((Category.assoc e.hom e.inv j.hom).symm.trans
            ((congrArg (fun k => k ≫ j.hom) e.hom_inv_id).trans
              (Category.id_comp j.hom)))).trans hj)))

end EtaleCohomology
