/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.FreeAbelianCohomologySections
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.PullbackCohomologySections
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Yoneda

/-!
# Inverse image of the original free abelian representables

The original inverse-image adjunction identifies the pullback of a
free abelian representable with the representable of the actual
base-changed étale object. This identification is natural in the
object and evaluates the original adjunction-unit pullback on sections.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The original adjunction and original free Yoneda equivalence
corepresent sections on the actual base-changed object. -/
def freeAbelianSheafYonedaPullbackHomEquiv (V : Y.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ((etaleAbelianPullback f).obj ((freeAbelianSheafYoneda Y.smallEtaleTopology).obj V) ⟶ F) ≃
      F.obj.obj (op ((etaleBaseChange f).obj V)) :=
  ((etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ F).trans
    (freeAbelianSheafYonedaHomEquiv Y.smallEtaleTopology V
      ((etaleAbelianPushforward f).obj F))

/-- Evaluation commutes with the original coefficient map. -/
theorem freeAbelianSheafYonedaPullbackHomEquiv_postcomp (V : Y.Etale)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (a : (etaleAbelianPullback f).obj
      ((freeAbelianSheafYoneda Y.smallEtaleTopology).obj V) ⟶ F) (η : F ⟶ G) :
    freeAbelianSheafYonedaPullbackHomEquiv f V G (a ≫ η) =
      η.hom.app (op ((etaleBaseChange f).obj V))
        (freeAbelianSheafYonedaPullbackHomEquiv f V F a) := by
  change freeAbelianSheafYonedaHomEquiv Y.smallEtaleTopology V _
    ((etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ _ (a ≫ η)) = _
  rw [Adjunction.homEquiv_naturality_right,
    freeAbelianSheafYonedaHomEquiv_postcomp]
  rfl

/-- Evaluation commutes with the original map between étale objects. -/
theorem freeAbelianSheafYonedaPullbackHomEquiv_precomp
    {V W : Y.Etale} (g : V ⟶ W)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : (etaleAbelianPullback f).obj
      ((freeAbelianSheafYoneda Y.smallEtaleTopology).obj W) ⟶ F) :
    freeAbelianSheafYonedaPullbackHomEquiv f V F
        ((etaleAbelianPullback f).map
          ((freeAbelianSheafYoneda Y.smallEtaleTopology).map g) ≫ a) =
      F.obj.map ((etaleBaseChange f).map g).op
        (freeAbelianSheafYonedaPullbackHomEquiv f W F a) := by
  change freeAbelianSheafYonedaHomEquiv Y.smallEtaleTopology V _
    ((etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ _
      ((etaleAbelianPullback f).map _ ≫ a)) = _
  rw [Adjunction.homEquiv_naturality_left,
    freeAbelianSheafYonedaHomEquiv_precomp]
  rfl

/-- The original inverse image carries a free abelian representable
to the free abelian representable of its actual base change. -/
def freeAbelianSheafYonedaPullbackIso (V : Y.Etale) :
    (etaleAbelianPullback f).obj
        ((freeAbelianSheafYoneda Y.smallEtaleTopology).obj V) ≅
      (freeAbelianSheafYoneda X.smallEtaleTopology).obj ((etaleBaseChange f).obj V) := by
  let E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤ Type u :=
    sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (evaluation _ _).obj (op ((etaleBaseChange f).obj V)) ⋙ forget AddCommGrpCat.{u}
  let e : E.CorepresentableBy ((etaleAbelianPullback f).obj
      ((freeAbelianSheafYoneda Y.smallEtaleTopology).obj V)) :=
    { homEquiv := freeAbelianSheafYonedaPullbackHomEquiv f V _
      homEquiv_comp := fun η a => freeAbelianSheafYonedaPullbackHomEquiv_postcomp f V a η }
  let e' : E.CorepresentableBy
      ((freeAbelianSheafYoneda X.smallEtaleTopology).obj ((etaleBaseChange f).obj V)) :=
    { homEquiv := freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology _ _
      homEquiv_comp := fun η a => freeAbelianSheafYonedaHomEquiv_postcomp
        X.smallEtaleTopology _ a η }
  exact e.uniqueUpToIso e'

/-- The inverse comparison preserves exactly the section supplied by
the original inverse-image adjunction. -/
theorem freeAbelianSheafYonedaPullbackIso_inv_comp (V : Y.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : (etaleAbelianPullback f).obj
      ((freeAbelianSheafYoneda Y.smallEtaleTopology).obj V) ⟶ F) :
    freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology _ F
        ((freeAbelianSheafYonedaPullbackIso f V).inv ≫ a) =
      freeAbelianSheafYonedaPullbackHomEquiv f V F a := by
  rw [freeAbelianSheafYonedaHomEquiv_postcomp]
  have he : freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology _ _
      (freeAbelianSheafYonedaPullbackIso f V).inv =
    freeAbelianSheafYonedaPullbackHomEquiv f V _ (𝟙 _) :=
      (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology _ _).apply_symm_apply _
  rw [he]
  exact (freeAbelianSheafYonedaPullbackHomEquiv_postcomp f V (𝟙 _) a).symm.trans
    (congrArg (freeAbelianSheafYonedaPullbackHomEquiv f V F) (Category.id_comp a))

/-- The actual representable comparison respects the original map
of base-changed étale objects. -/
theorem freeAbelianSheafYonedaPullbackIso_inv_naturality
    {V W : Y.Etale} (g : V ⟶ W) :
    (freeAbelianSheafYoneda X.smallEtaleTopology).map ((etaleBaseChange f).map g) ≫
        (freeAbelianSheafYonedaPullbackIso f W).inv =
      (freeAbelianSheafYonedaPullbackIso f V).inv ≫
        (etaleAbelianPullback f).map ((freeAbelianSheafYoneda Y.smallEtaleTopology).map g) := by
  apply (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology _ _).injective
  rw [freeAbelianSheafYonedaHomEquiv_precomp,
    freeAbelianSheafYonedaPullbackIso_inv_comp]
  have he : freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology _ _
      (freeAbelianSheafYonedaPullbackIso f W).inv =
    freeAbelianSheafYonedaPullbackHomEquiv f W _ (𝟙 _) :=
      (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology _ _).apply_symm_apply _
  rw [he]
  exact (freeAbelianSheafYonedaPullbackHomEquiv_precomp f g _ (𝟙 _)).symm.trans
    (congrArg (freeAbelianSheafYonedaPullbackHomEquiv f V _) (Category.comp_id _))

/-- On sections, the actual representable comparison gives the
original adjunction unit, with no replacement of the pullback map. -/
theorem freeAbelianSheafYonedaPullbackIso_section (V : Y.Etale)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (a : (freeAbelianSheafYoneda Y.smallEtaleTopology).obj V ⟶ F) :
    freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology _ _
        ((freeAbelianSheafYonedaPullbackIso f V).inv ≫ (etaleAbelianPullback f).map a) =
      ((etaleAbelianPullbackPushforwardAdjunction f).unit.app F).hom.app (op V)
        (freeAbelianSheafYonedaHomEquiv Y.smallEtaleTopology V F a) := by
  rw [freeAbelianSheafYonedaPullbackIso_inv_comp]
  let adj := etaleAbelianPullbackPushforwardAdjunction f
  let A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
    (freeAbelianSheafYoneda Y.smallEtaleTopology).obj V
  let E : (A ⟶ (etaleAbelianPushforward f).obj ((etaleAbelianPullback f).obj F)) ≃
      ((etaleAbelianPushforward f).obj ((etaleAbelianPullback f).obj F)).obj.obj (op V) :=
    freeAbelianSheafYonedaHomEquiv Y.smallEtaleTopology V _
  have hn : a ≫ adj.unit.app F =
      adj.unit.app A ≫ (etaleAbelianPushforward f).map ((etaleAbelianPullback f).map a) :=
    adj.unit.naturality a
  change E (adj.unit.app A ≫
    (etaleAbelianPushforward f).map ((etaleAbelianPullback f).map a)) = _
  exact (congrArg E hn.symm).trans
    (freeAbelianSheafYonedaHomEquiv_postcomp Y.smallEtaleTopology V a (adj.unit.app F))

/-- At a terminal object the representable comparison preserves the
original constant integer source of native cohomological pullback. -/
theorem freeAbelianSheafYonedaPullbackIso_terminal
    {T : Y.Etale} (hT : IsTerminal T) :
    (freeAbelianSheafYonedaPullbackIso f T).inv ≫
        (etaleAbelianPullback f).map
          (freeAbelianSheafYonedaTerminalIso Y.smallEtaleTopology hT).hom =
      (freeAbelianSheafYonedaTerminalIso X.smallEtaleTopology
        (hT.isTerminalObj (etaleBaseChange f) T)).hom ≫
          ((etaleAbelianPullbackConstantIso f).app
            (AddCommGrpCat.of (ULift.{u} ℤ))).inv := by
  let A : AddCommGrpCat.{u} := AddCommGrpCat.of (ULift.{u} ℤ)
  let Z : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let U : X.Etale := (etaleBaseChange f).obj T
  apply (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology U _).injective
  rw [freeAbelianSheafYonedaPullbackIso_section]
  have he : freeAbelianSheafYonedaHomEquiv Y.smallEtaleTopology T Z
      (freeAbelianSheafYonedaTerminalIso Y.smallEtaleTopology hT).hom =
      (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app
        (op T) (ULift.up (1 : ℤ)) := by
    let adj := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u} hT
    have hu : adj.homEquiv A Z (𝟙 Z) = adj.unit.app A := by
      let E := (sheafSections Y.smallEtaleTopology AddCommGrpCat.{u}).obj (op T)
      let η : A ⟶ E.obj Z := adj.unit.app A
      have hmap : E.map (𝟙 Z) = 𝟙 (E.obj Z) := E.map_id Z
      exact (congrArg (fun q : E.obj Z ⟶ E.obj Z => η ≫ q) hmap).trans
        (Category.comp_id η)
    have hunit : adj.unit.app A =
        (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app
          (op T) := by
      change ((constantPresheafAdj AddCommGrpCat.{u} hT).comp
        (sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u})).unit.app A = _
      rw [Adjunction.comp_unit_app]
      rfl
    have he := freeAbelianSheafYonedaTerminalIso_homEquiv
      Y.smallEtaleTopology hT Z (𝟙 Z)
    have hid := congrArg (freeAbelianSheafYonedaHomEquiv Y.smallEtaleTopology T Z)
      (Category.comp_id (freeAbelianSheafYonedaTerminalIso Y.smallEtaleTopology hT).hom)
    exact hid.symm.trans
      (he.trans (congrArg (fun q : A ⟶ Z.obj.obj (op T) => q (ULift.up (1 : ℤ)))
        (hu.trans hunit)))
  rw [he, freeAbelianSheafYonedaTerminalIso_homEquiv]
  change ((etaleAbelianPullbackPushforwardAdjunction f).unit.app Z).hom.app (op T)
      ((toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app
        (op T) (ULift.up (1 : ℤ))) =
    (((etaleAbelianPullbackConstantIso f).app A).inv).hom.app (op U)
      ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app
        (op U) (ULift.up (1 : ℤ)))
  have hs := etaleAbelianConstantHom_pullback_section f A Z (𝟙 Z) T U (𝟙 U)
  let E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := (etaleAbelianPullback f).obj Z
  let C : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let β : C ⟶ E := ((etaleAbelianPullbackConstantIso f).app A).inv
  let η : Z.obj.obj (op T) ⟶ E.obj.obj (op U) :=
    ((etaleAbelianPullbackPushforwardAdjunction f).unit.app Z).hom.app (op T)
  let x : C.obj.obj (op U) :=
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app
      (op U) (ULift.up (1 : ℤ))
  let y : Z.obj.obj (op T) :=
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app
      (op T) (ULift.up (1 : ℤ))
  have hL : (etaleAbelianPullback f).map (𝟙 Z) = 𝟙 E :=
    (etaleAbelianPullback f).map_id Z
  have hβ : β ≫ (etaleAbelianPullback f).map (𝟙 Z) = β :=
    (congrArg (fun q : E ⟶ E => β ≫ q) hL).trans (Category.comp_id β)
  have hZ : (𝟙 Z : Z ⟶ Z).hom.app (op T) = 𝟙 (Z.obj.obj (op T)) := rfl
  have hmap : E.obj.map (𝟙 U).op = 𝟙 (E.obj.obj (op U)) := E.obj.map_id (op U)
  have hp := congrArg (fun q : A ⟶ E.obj.obj (op U) => q (ULift.up (1 : ℤ))) hs
  have hleft : (β ≫ (etaleAbelianPullback f).map (𝟙 Z)).hom.app (op U) x =
      β.hom.app (op U) x :=
    congrArg (fun q : C ⟶ E => q.hom.app (op U) x) hβ
  have hright : E.obj.map (𝟙 U).op (η ((𝟙 Z : Z ⟶ Z).hom.app (op T) y)) = η y :=
    (ConcreteCategory.congr_hom hmap _).trans
      (congrArg η (ConcreteCategory.congr_hom hZ y))
  exact hright.symm.trans (hp.symm.trans hleft)

end EtaleCohomology
