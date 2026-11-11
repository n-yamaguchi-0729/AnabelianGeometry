/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSectionMaps
public import Nyll.EtaleCohomology.Sites.GeometricallyConnectedSections
public import Nyll.EtaleCohomology.Sites.ModuleRestriction
public import Nyll.EtaleCohomology.Sites.PullbackComposition
public import Nyll.EtaleCohomology.Sites.PullbackSectionComposition
public import Nyll.EtaleCohomology.Sites.PullbackSections
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# The original unit under geometrically connected pullback

Unique section descent remains valid after every étale base change.
The original section-composition identities therefore make every component
of the inverse-image/direct-image unit invertible. All comparisons retain
the actual adjunction units and the actual base-changed étale objects.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- Localizing at an étale object's own identity section is an isomorphism
for the original inverse-image section map. -/
private theorem etalePullbackSectionMap_identity_isIso
    {X : Scheme.{u}} (R : Type u) [CommRing R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (V : X.Etale) :
    IsIso (etalePullbackSectionMap V.hom R F
      (U := Scheme.Etale.mk (𝟙 V.left)) (V := V) (𝟙 V.left) rfl) := by
  let U : V.left.Etale := Scheme.Etale.mk (𝟙 V.left)
  let G : Sheaf V.left.smallEtaleTopology (ModuleCat.{u} R) :=
    (etalePullback V.hom R).obj F
  let e : (etalePostcompose V.hom).obj U ≅ V :=
    MorphismProperty.Over.isoMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      (Iso.refl V.left) rfl
  let c : G.obj.obj (op U) ≅
      F.obj.obj (op ((etalePostcompose V.hom).obj U)) :=
    ((sheafSections V.left.smallEtaleTopology (ModuleCat.{u} R)).obj (op U)).mapIso
      ((etalePullbackRestrictionIso V.hom R).app F)
  let a : F.obj.obj (op V) ⟶ G.obj.obj (op U) :=
    etalePullbackSectionMap V.hom R F (U := U) (V := V) (𝟙 V.left) rfl
  have h : a ≫ c.hom = F.obj.map e.hom.op :=
    etalePullbackSectionMap_restrictionIso V.hom R F
      (U := V) (V := U) (𝟙 V.left) rfl
  have : IsIso (F.obj.map e.hom.op) :=
    inferInstanceAs (IsIso (F.obj.mapIso e.op).hom)
  exact IsIso.of_isIso_fac_right h

/-- Unique descent makes the actual base-change section map invertible. -/
private theorem etaleGeometricallyConnected_baseChangeSectionMap_isIso
    {X Y : Scheme.{u}} (q : Y ⟶ X) [Flat q] [QuasiCompact q] [GeometricallyConnected q]
    (R : Type u) [CommRing R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (V : X.Etale) :
    let v : V.left ⟶ X := V.hom
    let _ : Etale v := V.prop
    let Z : Scheme.{u} := pullback v q
    let w : Z ⟶ Y := pullback.snd v q
    let W : Y.Etale := MorphismProperty.Over.mk
      (P := show MorphismProperty Scheme.{u} from @Etale) ⊤ w inferInstance
    IsIso (etalePullbackSectionMap q R F (U := W) (V := V)
      (pullback.fst v q) pullback.condition) := by
  intro v hv Z w W
  let U : Z.Etale := Scheme.Etale.mk (𝟙 Z)
  let r : Z ⟶ V.left := pullback.fst v q
  let h : r ≫ v = w ≫ q := pullback.condition
  let t : Z ⟶ X := w ≫ q
  let hn : r ≫ v = (𝟙 Z) ≫ t := h.trans (Category.id_comp t).symm
  let Fv : Sheaf V.left.smallEtaleTopology (ModuleCat.{u} R) :=
    (etalePullback v R).obj F
  let G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R) := (etalePullback q R).obj F
  let Q : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
    (sheafSections Z.smallEtaleTopology (ModuleCat.{u} R)).obj (op U)
  let a : F.obj.obj (op V) ⟶ G.obj.obj (op W) :=
    etalePullbackSectionMap q R F (U := W) (V := V) r h
  let b : G.obj.obj (op W) ⟶ Q.obj ((etalePullback w R).obj G) :=
    etalePullbackSectionMap w R G (U := U) (V := W) (𝟙 Z) rfl
  let av : F.obj.obj (op V) ⟶ Fv.obj.obj (op (Scheme.Etale.mk (𝟙 V.left))) :=
    etalePullbackSectionMap v R F
      (U := Scheme.Etale.mk (𝟙 V.left)) (V := V) (𝟙 V.left) rfl
  let g : Fv.obj.obj (op (Scheme.Etale.mk (𝟙 V.left))) ⟶
      Q.obj ((etalePullback r R).obj Fv) :=
    etalePullbackGlobalSectionsMap r R Fv
  let c : F.obj.obj (op V) ⟶ Q.obj ((etalePullback t R).obj F) :=
    etalePullbackSectionMap t R F (U := U) (V := V) r hn
  let I₁ : etalePullback v R ⋙ etalePullback r R ≅ etalePullback t R :=
    (etalePullbackCompIso r v R).symm ≪≫
      eqToIso (congrArg (fun k : Z ⟶ X => etalePullback k R) h)
  let I₂ : etalePullback q R ⋙ etalePullback w R ≅ etalePullback t R :=
    (etalePullbackCompIso w q R).symm ≪≫
      eqToIso (congrArg (fun k : Z ⟶ X => etalePullback k R)
        (show w ≫ q = t from rfl))
  let E₁ : (etalePullback r R).obj Fv ≅ (etalePullback t R).obj F := I₁.app F
  let E₂ : (etalePullback w R).obj G ≅ (etalePullback t R).obj F := I₂.app F
  let e₁ : Q.obj ((etalePullback r R).obj Fv) ≅ Q.obj ((etalePullback t R).obj F) :=
    Q.mapIso E₁
  let e₂ : Q.obj ((etalePullback w R).obj G) ≅ Q.obj ((etalePullback t R).obj F) :=
    Q.mapIso E₂
  have : Flat r := inferInstanceAs (Flat (pullback.fst v q))
  have : QuasiCompact r := inferInstanceAs (QuasiCompact (pullback.fst v q))
  have : GeometricallyConnected r :=
    inferInstanceAs (GeometricallyConnected (pullback.fst v q))
  have : IsIso av := etalePullbackSectionMap_identity_isIso R F V
  have : IsIso b := etalePullbackSectionMap_identity_isIso R G W
  have : IsIso g :=
    (ConcreteCategory.isIso_iff_bijective g).mpr
      (etalePullbackGlobalSectionsMap_bijective_of_geometricallyConnected r R Fv)
  have h₁ : av ≫ g ≫ e₁.hom = c :=
    etalePullbackSectionMap_comp_congr r v R t h F
      (U := U) (V := Scheme.Etale.mk (𝟙 V.left)) (W := V)
      r ((Category.comp_id r).trans (Category.id_comp r).symm)
      (𝟙 V.left) rfl r hn (Category.comp_id r)
  let Ciso : F.obj.obj (op V) ≅ Q.obj ((etalePullback t R).obj F) :=
    asIso av ≪≫ asIso g ≪≫ e₁
  have hC : Ciso.hom = c := h₁
  have : IsIso c := hC ▸ (inferInstance : IsIso Ciso.hom)
  have h₂ : a ≫ b ≫ e₂.hom = c :=
    etalePullbackSectionMap_comp_congr w q R t rfl F
      (U := U) (V := W) (W := V)
      (𝟙 Z) rfl r h r hn (Category.id_comp r)
  let Biso : G.obj.obj (op W) ≅ Q.obj ((etalePullback t R).obj F) := asIso b ≪≫ e₂
  have hB : a ≫ Biso.hom = c := h₂
  exact IsIso.of_isIso_fac_right hB

/-- Every component of the original unit is invertible: section descent on
the actual étale base change gives the inverse. -/
theorem etaleGeometricallyConnected_unit_app_isIso
    {X Y : Scheme.{u}} (q : Y ⟶ X) [Flat q] [QuasiCompact q] [GeometricallyConnected q]
    (R : Type u) [CommRing R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (V : X.Etale) :
    IsIso (((etalePullbackPushforwardAdjunction q R).unit.app F).hom.app (op V)) := by
  let v : V.left ⟶ X := V.hom
  let hv : Etale v := V.prop
  let Z : Scheme.{u} := pullback v q
  let w : Z ⟶ Y := pullback.snd v q
  let W : Y.Etale := MorphismProperty.Over.mk
    (P := show MorphismProperty Scheme.{u} from @Etale) ⊤ w inferInstance
  let r : Z ⟶ V.left := pullback.fst v q
  let h : r ≫ v = w ≫ q := pullback.condition
  let G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R) := (etalePullback q R).obj F
  let η : F ⟶ (etalePushforward q R).obj G :=
    (etalePullbackPushforwardAdjunction q R).unit.app F
  let ηV : F.obj.obj (op V) ⟶ G.obj.obj (op W) := η.hom.app (op V)
  let a : F.obj.obj (op V) ⟶ G.obj.obj (op W) :=
    etalePullbackSectionMap q R F (U := W) (V := V) r h
  have : IsIso a := etaleGeometricallyConnected_baseChangeSectionMap_isIso q R F V
  have hm : etaleBaseChangeLift q (U := W) (V := V) r h = 𝟙 W := by
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift r w h = 𝟙 Z
    apply pullback.hom_ext
    · exact (pullback.lift_fst r w h).trans
        (Category.id_comp (pullback.fst v q)).symm
    · exact (pullback.lift_snd r w h).trans
        (Category.id_comp (pullback.snd v q)).symm
  have hmap : G.obj.map (𝟙 W).op = 𝟙 (G.obj.obj (op W)) := G.obj.map_id (op W)
  have ha : a = ηV := by
    change ηV ≫ G.obj.map (etaleBaseChangeLift q r h).op = ηV
    exact (congrArg (fun k : W ⟶ W => ηV ≫ G.obj.map k.op) hm).trans
      ((congrArg (fun k : G.obj.obj (op W) ⟶ G.obj.obj (op W) => ηV ≫ k) hmap).trans
        (Category.comp_id ηV))
  have hηV : IsIso ηV := ha ▸ (inferInstance : IsIso a)
  exact hηV

/-- Flat quasi-compact geometrically connected pullback preserves the
entire original sheaf through its actual inverse-image/direct-image unit. -/
theorem etaleGeometricallyConnected_unit_isIso
    {X Y : Scheme.{u}} (q : Y ⟶ X) [Flat q] [QuasiCompact q] [GeometricallyConnected q]
    (R : Type u) [CommRing R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    IsIso ((etalePullbackPushforwardAdjunction q R).unit.app F) := by
  let η : F ⟶ (etalePushforward q R).obj ((etalePullback q R).obj F) :=
    (etalePullbackPushforwardAdjunction q R).unit.app F
  have : ∀ V : X.Etaleᵒᵖ, IsIso (η.hom.app V) := fun V =>
    etaleGeometricallyConnected_unit_app_isIso q R F V.unop
  have : IsIso η.hom := NatIso.isIso_of_isIso_app η.hom
  exact (ObjectProperty.isIso_hom_iff η).mp (inferInstance : IsIso η.hom)

end EtaleCohomology
