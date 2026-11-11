/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.ModuleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.PullbackSections
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Actual pulled sections under the étale restriction identification

The chosen inverse-image unit and the canonical restriction isomorphism
carry a pulled section to its ordinary restriction along the original
local factor. The proof uses adjunction uniqueness and the actual
base-change counit on the small étale sites.
-/

@[expose] public section

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

private theorem sectionRestrictionDiagram
    {A : Type*} [Category A] {S T U V W : A}
    (η : S ⟶ T) (a : T ⟶ U) (e : U ⟶ V) (e' : T ⟶ W)
    (r : W ⟶ V) (c : S ⟶ W) (k : S ⟶ V)
    (hn : a ≫ e = e' ≫ r) (hη : η ≫ e' = c) (hr : c ≫ r = k) :
    (η ≫ a) ≫ e = k := by
  rw [Category.assoc, hn, ← Category.assoc, hη, hr]

variable {X Y : Scheme.{u}} (q : Y ⟶ X) [Etale q]

/-- The actual restriction adjunction unit is the original site counit on sections,
for arbitrary coefficient categories. -/
theorem etaleRestrictionUnit_app
    {A : Type v} [Category.{w} A]
    (F : Sheaf X.smallEtaleTopology A) (U : X.Etale) :
    ((etaleRestrictionPushforwardAdjunction q A).unit.app F).hom.app
        (op U) = F.obj.map ((etalePostcomposeBaseChangeAdjunction q).counit.app U).op := by
  change (𝟙 _) ≫ F.obj.map
    ((etalePostcomposeBaseChangeAdjunction q).counit.app U).op ≫ (𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]

/-- The original site counit cancels the actual lifted local factor. -/
theorem etalePostcomposeBaseChangeLift_counit
    {U : X.Etale} {V : Y.Etale}
    (l : V.left ⟶ U.left) (hl : l ≫ U.hom = V.hom ≫ q) :
    (etalePostcompose q).map (etaleBaseChangeLift q l hl) ≫
        (etalePostcomposeBaseChangeAdjunction q).counit.app U =
      MorphismProperty.Over.homMk
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
        (A := (etalePostcompose q).obj V) (B := U) l hl := by
  apply MorphismProperty.Over.Hom.ext
  change pullback.lift l V.hom hl ≫ pullback.fst U.hom q = l
  exact pullback.lift_fst _ _ _

variable (R : Type u) [CommRing R]

private theorem pullbackRestrictionUnit_app
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (U : X.Etale) :
    ((etalePullbackPushforwardAdjunction q R).unit.app F).hom.app (op U) ≫
      ((etalePullbackRestrictionIso q R).hom.app F).hom.app
        (op ((etaleBaseChange q).obj U)) =
      F.obj.map ((etalePostcomposeBaseChangeAdjunction q).counit.app U).op := by
  exact (congrArg (fun a => a.hom.app (op U))
    (Adjunction.unit_leftAdjointUniq_hom_app
      (etalePullbackPushforwardAdjunction q R)
      (etaleRestrictionPushforwardAdjunction q (ModuleCat.{u} R)) F)).trans
        (etaleRestrictionUnit_app q F U)

/-- Under the canonical restriction identification, the actual pulled
section is the ordinary restriction along its original local factor. -/
theorem etalePullbackSectionMap_restrictionIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    {U : X.Etale} {V : Y.Etale}
    (l : V.left ⟶ U.left) (hl : l ≫ U.hom = V.hom ≫ q) :
    etalePullbackSectionMap q R F l hl ≫
        ((etalePullbackRestrictionIso q R).hom.app F).hom.app (op V) =
      F.obj.map (MorphismProperty.Over.homMk
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
        (A := (etalePostcompose q).obj V) (B := U) l hl).op := by
  apply sectionRestrictionDiagram
    (((etalePullbackPushforwardAdjunction q R).unit.app F).hom.app (op U))
    (((etalePullback q R).obj F).obj.map (etaleBaseChangeLift q l hl).op)
    (((etalePullbackRestrictionIso q R).hom.app F).hom.app (op V))
    (((etalePullbackRestrictionIso q R).hom.app F).hom.app
      (op ((etaleBaseChange q).obj U)))
    (F.obj.map ((etalePostcompose q).map (etaleBaseChangeLift q l hl)).op)
    (F.obj.map ((etalePostcomposeBaseChangeAdjunction q).counit.app U).op)
  · exact ((etalePullbackRestrictionIso q R).hom.app F).hom.naturality
      (etaleBaseChangeLift q l hl).op
  · exact pullbackRestrictionUnit_app q R F U
  · exact (F.obj.map_comp _ _).symm.trans
      (congrArg (fun a => F.obj.map a.op) (etalePostcomposeBaseChangeLift_counit q l hl))

omit [Etale q] in
/-- Pulling global sections through a scheme isomorphism is invertible
for the actual inverse-image unit map. -/
theorem etalePullbackGlobalSectionsMap_isIso_of_isIso [IsIso q]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    IsIso (etalePullbackGlobalSectionsMap q R F) := by
  let e₀ : Y ≅ X := asIso q
  let e : (etalePostcompose q).obj (Scheme.Etale.mk (𝟙 Y)) ≅
      Scheme.Etale.mk (𝟙 X) := MorphismProperty.Over.isoMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) e₀
    ((Category.comp_id q).trans (Category.id_comp q).symm)
  let eR := ((sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u} R)).mapIso
    ((etalePullbackRestrictionIso q R).app F)).app (op (Scheme.Etale.mk (𝟙 Y)))
  have h : etalePullbackGlobalSectionsMap q R F ≫ eR.hom = F.obj.map e.hom.op :=
    etalePullbackSectionMap_restrictionIso q R F
      (U := Scheme.Etale.mk (𝟙 X)) (V := Scheme.Etale.mk (𝟙 Y)) q
      ((Category.comp_id q).trans (Category.id_comp q).symm)
  have : IsIso (etalePullbackGlobalSectionsMap q R F ≫ eR.hom) := by
    rw [h]
    exact inferInstanceAs (IsIso (F.obj.mapIso e.op).hom)
  exact IsIso.of_isIso_comp_right (etalePullbackGlobalSectionsMap q R F) eR.hom

end EtaleCohomology
