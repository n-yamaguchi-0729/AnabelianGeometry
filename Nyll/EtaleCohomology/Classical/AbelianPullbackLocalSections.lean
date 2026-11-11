/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Classical.PullbackCohomologySections
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.PullbackSections
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Original abelian H⁰ pullback on local sections

The actual inverse-image unit pulls local sections through any commuting
scheme square. Its naturality identifies the local section of the
original cohomological pullback, including after a specified original
coefficient morphism. This applies to closed graph maps without any
dominance hypothesis.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The actual abelian inverse-image unit followed by a local factor. -/
def etaleAbelianPullbackLocalSectionMap
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : X.Etale} {W : Y.Etale} (l : W.left ⟶ V.left)
    (hl : l ≫ V.hom = W.hom ≫ f) :
    F.obj.obj (op V) ⟶ ((etaleAbelianPullback f).obj F).obj.obj (op W) :=
  ((etaleAbelianPullbackPushforwardAdjunction f).unit.app F).hom.app (op V) ≫
    ((etaleAbelianPullback f).obj F).obj.map (etaleBaseChangeLift f l hl).op

private theorem baseChangeIdentity_hom_ext
    {W : Y.Etale}
    (a b : W ⟶ (etaleBaseChange f).obj (Scheme.Etale.mk (𝟙 X))) : a = b := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono (pullback.snd (𝟙 X) f)).mp
  exact a.w.trans b.w.symm

/-- Local pullback of a restricted global section is restriction of its
original global pullback. -/
theorem etaleAbelianPullbackLocalSectionMap_global_restriction
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : X.Etale} {W : Y.Etale} (t : V ⟶ Scheme.Etale.mk (𝟙 X))
    (l : W.left ⟶ V.left) (hl : l ≫ V.hom = W.hom ≫ f) :
    F.obj.map t.op ≫ etaleAbelianPullbackLocalSectionMap f F l hl =
      etaleAbelianPullbackLocalSectionMap f F f
          ((Category.comp_id f).trans (Category.id_comp f).symm) ≫
        ((etaleAbelianPullback f).obj F).obj.map
          (MorphismProperty.Over.homMk
            (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
            (A := W) (B := Scheme.Etale.mk (𝟙 Y))
            W.hom (Category.comp_id W.hom)).op := by
  let H := ((etaleAbelianPullback f).obj F).obj
  let V₀ : X.Etale := Scheme.Etale.mk (𝟙 X)
  let W₀ : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  let a : W ⟶ (etaleBaseChange f).obj V := etaleBaseChangeLift f l hl
  let b : W₀ ⟶ (etaleBaseChange f).obj V₀ :=
    etaleBaseChangeLift f f ((Category.comp_id f).trans (Category.id_comp f).symm)
  let j : W ⟶ W₀ := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    W.hom (Category.comp_id W.hom)
  let tf : (etaleBaseChange f).obj V ⟶ (etaleBaseChange f).obj V₀ :=
    (etaleBaseChange f).map t
  have hab : a ≫ tf = j ≫ b := baseChangeIdentity_hom_ext f _ _
  let uV : F.obj.obj (op V) ⟶ H.obj (op ((etaleBaseChange f).obj V)) :=
    ((etaleAbelianPullbackPushforwardAdjunction f).unit.app F).hom.app (op V)
  let u₀ : F.obj.obj (op V₀) ⟶ H.obj (op ((etaleBaseChange f).obj V₀)) :=
    ((etaleAbelianPullbackPushforwardAdjunction f).unit.app F).hom.app (op V₀)
  have hunit : F.obj.map t.op ≫ uV = u₀ ≫ H.map tf.op :=
    ((etaleAbelianPullbackPushforwardAdjunction f).unit.app F).hom.naturality t.op
  have hmap : H.map tf.op ≫ H.map a.op = H.map b.op ≫ H.map j.op := by
    calc
      H.map tf.op ≫ H.map a.op = H.map (a ≫ tf).op :=
        (H.map_comp tf.op a.op).symm
      _ = H.map (j ≫ b).op := congrArg (fun k => H.map k.op) hab
      _ = H.map b.op ≫ H.map j.op := H.map_comp b.op j.op
  change F.obj.map t.op ≫ (uV ≫ H.map a.op) =
    (u₀ ≫ H.map b.op) ≫ H.map j.op
  rw [← Category.assoc, hunit, Category.assoc, hmap, ← Category.assoc]

/-- Applying a coefficient morphism to local pullback is its actual
direct-image adjoint followed by local restriction. -/
theorem etaleAbelianPullbackLocalSectionMap_coeff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (φ : (etaleAbelianPullback f).obj F ⟶ G)
    {V : X.Etale} {W : Y.Etale} (l : W.left ⟶ V.left)
    (hl : l ≫ V.hom = W.hom ≫ f) :
    etaleAbelianPullbackLocalSectionMap f F l hl ≫ φ.hom.app (op W) =
      ((etaleAbelianPullbackPushforwardAdjunction f).homEquiv F G φ).hom.app (op V) ≫
        G.obj.map (etaleBaseChangeLift f l hl).op := by
  let H := ((etaleAbelianPullback f).obj F).obj
  let η : F ⟶ (etaleAbelianPushforward f).obj ((etaleAbelianPullback f).obj F) :=
    (etaleAbelianPullbackPushforwardAdjunction f).unit.app F
  let m : W ⟶ (etaleBaseChange f).obj V := etaleBaseChangeLift f l hl
  let uV : F.obj.obj (op V) ⟶ H.obj (op ((etaleBaseChange f).obj V)) :=
    η.hom.app (op V)
  have hφ : H.map m.op ≫ φ.hom.app (op W) =
      φ.hom.app (op ((etaleBaseChange f).obj V)) ≫ G.obj.map m.op :=
    φ.hom.naturality m.op
  have ha : ((etaleAbelianPullbackPushforwardAdjunction f).homEquiv F G φ).hom.app
      (op V) = uV ≫ φ.hom.app (op ((etaleBaseChange f).obj V)) := by
    have he : (etaleAbelianPullbackPushforwardAdjunction f).homEquiv F G φ =
        η ≫ (etaleAbelianPushforward f).map φ := by
      rw [Adjunction.homEquiv_unit]
    exact congrArg
      (fun q : F ⟶ (etaleAbelianPushforward f).obj G => q.hom.app (op V)) he
  change (uV ≫ H.map m.op) ≫ φ.hom.app (op W) = _
  rw [Category.assoc, hφ, ← Category.assoc, ← ha]
  rfl

/-- Every local section of original abelian H⁰ pullback is the actual
inverse-image section of the original restricted terminal section. -/
theorem etaleAbelianCohomologyPullbackMap_zero_local_sections
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : X.Etale} {W : Y.Etale} (l : W.left ⟶ V.left)
    (hl : l ≫ V.hom = W.hom ≫ f) (a : Sheaf.H.{u} F 0) :
    let hX := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    let hY := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) Y
    ((etaleAbelianPullback f).obj F).obj.map (hY.from W).op
        (Sheaf.H.equiv₀ ((etaleAbelianPullback f).obj F) hY
          (etaleAbelianCohomologyPullbackMap f F 0 a)) =
      etaleAbelianPullbackLocalSectionMap f F l hl
        (F.obj.map (hX.from V).op (Sheaf.H.equiv₀ F hX a)) := by
  intro hX hY
  let b : Scheme.Etale.mk (𝟙 Y) ⟶ (etaleBaseChange f).obj (Scheme.Etale.mk (𝟙 X)) :=
    etaleBaseChangeLift f f ((Category.comp_id f).trans (Category.id_comp f).symm)
  let j : W ⟶ Scheme.Etale.mk (𝟙 Y) := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    W.hom (Category.comp_id W.hom)
  have hj : hY.from W = j := hY.hom_ext _ _
  rw [hj, etaleAbelianCohomologyPullbackMap_zero_sections f F hX hY b]
  exact (ConcreteCategory.congr_hom
    (etaleAbelianPullbackLocalSectionMap_global_restriction f F (hX.from V) l hl)
      (Sheaf.H.equiv₀ F hX a)).symm

/-- The original H⁰ pullback with coefficients is computed locally by
the actual direct-image adjoint of those coefficients. -/
theorem etaleAbelianCohomologyPullbackCoeff_zero_local_sections
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (φ : (etaleAbelianPullback f).obj F ⟶ G)
    {V : X.Etale} {W : Y.Etale} (l : W.left ⟶ V.left)
    (hl : l ≫ V.hom = W.hom ≫ f) (a : Sheaf.H.{u} F 0) :
    let hX := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    let hY := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) Y
    G.obj.map (hY.from W).op
        (Sheaf.H.equiv₀ G hY
          (Sheaf.H.map φ 0 (etaleAbelianCohomologyPullbackMap f F 0 a))) =
      G.obj.map (etaleBaseChangeLift f l hl).op
        (((etaleAbelianPullbackPushforwardAdjunction f).homEquiv F G φ).hom.app (op V)
          (F.obj.map (hX.from V).op (Sheaf.H.equiv₀ F hX a))) := by
  intro hX hY
  let b : Sheaf.H.{u} ((etaleAbelianPullback f).obj F) 0 :=
    etaleAbelianCohomologyPullbackMap f F 0 a
  let s : ((etaleAbelianPullback f).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y))) :=
    Sheaf.H.equiv₀.{u} ((etaleAbelianPullback f).obj F) hY b
  let r : F.obj.obj (op V) := F.obj.map (hX.from V).op (Sheaf.H.equiv₀.{u} F hX a)
  have hn := ConcreteCategory.congr_hom (φ.hom.naturality (hY.from W).op) s
  have hnat : φ.hom.app (op (Scheme.Etale.mk (𝟙 Y))) s =
      Sheaf.H.equiv₀.{u} G hY (Sheaf.H.map φ 0 b) :=
    Sheaf.H.equiv₀_naturality.{u} (J := Y.smallEtaleTopology)
      (F := (etaleAbelianPullback f).obj F) (G := G) hY φ b
  have hlocal : ((etaleAbelianPullback f).obj F).obj.map (hY.from W).op s =
      etaleAbelianPullbackLocalSectionMap f F l hl r :=
    etaleAbelianCohomologyPullbackMap_zero_local_sections f F l hl a
  have hcoeff := ConcreteCategory.congr_hom
    (etaleAbelianPullbackLocalSectionMap_coeff f F G φ l hl) r
  exact (congrArg (G.obj.map (hY.from W).op) hnat.symm).trans
    (hn.symm.trans ((congrArg (φ.hom.app (op W)) hlocal).trans hcoeff))

end EtaleCohomology
