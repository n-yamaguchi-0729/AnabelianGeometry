/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianRestrictionPullback
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Actual global sections of finite-cover generic-unit restriction

The original degree-zero pullback is evaluated at the original terminal
objects. Its restriction to any further étale source is the same quotient
comparison applied to the original base section on that source.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups

namespace EtaleCohomology

variable {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
  (Y : FiniteEtale X) [IsConnected Y] [IsIntegral Y.left]

/-- Restriction of an actual original global quotient section to the
actual connected finite cover. -/
def finiteGenericUnitGlobalSectionsMap :
    (etaleGenericUnitQuotient X).obj.obj (op (Scheme.Etale.mk (𝟙 X))) →+
      (etaleGenericUnitQuotient Y.left).obj.obj (op (Scheme.Etale.mk (𝟙 Y.left))) :=
  (ConcreteCategory.hom
    ((etaleRestrictionFiniteGenericUnitQuotientIso Y).hom.hom.app
      (op (Scheme.Etale.mk (𝟙 Y.left))))).comp
    (ConcreteCategory.hom ((etaleGenericUnitQuotient X).obj.map
      ((MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) X).from
          ((etalePostcompose Y.hom).obj (Scheme.Etale.mk (𝟙 Y.left)))).op))

/-- Every further source retains the original quotient section. -/
theorem finiteGenericUnitGlobalSectionsMap_restrict
    (V : Y.left.Etale)
    (s : (etaleGenericUnitQuotient X).obj.obj (op (Scheme.Etale.mk (𝟙 X)))) :
    (etaleGenericUnitQuotient Y.left).obj.map
        ((MorphismProperty.Over.mkIdTerminal
          (show MorphismProperty Scheme.{u} from @Etale) Y.left).from V).op
        (finiteGenericUnitGlobalSectionsMap Y s) =
      (etaleRestrictionFiniteGenericUnitQuotientIso Y).hom.hom.app (op V)
        ((etaleGenericUnitQuotient X).obj.map
          ((MorphismProperty.Over.mkIdTerminal
            (show MorphismProperty Scheme.{u} from @Etale) X).from
              ((etalePostcompose Y.hom).obj V)).op s) := by
  let p : Y.left ⟶ X := Y.hom
  let hX := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let hY := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) Y.left
  let Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := etaleGenericUnitQuotient X
  let R : Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u} :=
    (etaleRestriction p AddCommGrpCat.{u}).obj Q
  let T : Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u} := etaleGenericUnitQuotient Y.left
  let e : R ≅ T := etaleRestrictionFiniteGenericUnitQuotientIso Y
  let v := Scheme.Etale.mk (𝟙 Y.left)
  let r := hX.from ((etalePostcompose p).obj v)
  let j := hY.from V
  have hm : (etalePostcompose p).map j ≫ r =
      hX.from ((etalePostcompose p).obj V) := hX.hom_ext _ _
  have hc : Q.obj.map r.op ≫ Q.obj.map ((etalePostcompose p).map j).op =
      Q.obj.map (hX.from ((etalePostcompose p).obj V)).op :=
    (Q.obj.map_comp r.op ((etalePostcompose p).map j).op).symm.trans
      (congrArg
        (fun z : (etalePostcompose p).obj V ⟶ Scheme.Etale.mk (𝟙 X) =>
          Q.obj.map z.op) hm)
  have hh : R.obj.map j.op (Q.obj.map r.op s) =
      Q.obj.map (hX.from ((etalePostcompose p).obj V)).op s :=
    ConcreteCategory.congr_hom hc s
  have hn : e.hom.hom.app (op V) (R.obj.map j.op (Q.obj.map r.op s)) =
      T.obj.map j.op (finiteGenericUnitGlobalSectionsMap Y s) :=
    ConcreteCategory.congr_hom (e.hom.hom.naturality j.op) (Q.obj.map r.op s)
  exact hn.symm.trans
    (congrArg (fun t : R.obj.obj (op V) => e.hom.hom.app (op V) t) hh)

/-- The native H⁰ pullback evaluates to the same actual global section. -/
theorem finiteGenericUnitH0Pullback_sections
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0) :
    Sheaf.H.equiv₀ (etaleGenericUnitQuotient Y.left)
        (MorphismProperty.Over.mkIdTerminal
          (show MorphismProperty Scheme.{u} from @Etale) Y.left)
        (finiteGenericUnitH0Pullback Y a) =
      finiteGenericUnitGlobalSectionsMap Y
        (Sheaf.H.equiv₀ (etaleGenericUnitQuotient X)
          (MorphismProperty.Over.mkIdTerminal
            (show MorphismProperty Scheme.{u} from @Etale) X) a) := by
  let p : Y.left ⟶ X := Y.hom
  let hX := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let hY := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) Y.left
  let Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := etaleGenericUnitQuotient X
  let A : Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u} :=
    (etaleAbelianPullback p).obj Q
  let B : Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u} :=
    (etaleRestriction p AddCommGrpCat.{u}).obj Q
  let C : Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u} := etaleGenericUnitQuotient Y.left
  let e : A ≅ B := (etaleAbelianPullbackRestrictionIso p).app Q
  let t : B ≅ C := etaleRestrictionFiniteGenericUnitQuotientIso Y
  let b : Sheaf.H.{u} A 0 := etaleAbelianCohomologyPullbackMap p Q 0 a
  let c : Sheaf.H.{u} B 0 := etaleAbelianRestrictionCohomologyPullback p Q 0 a
  have hp : finiteGenericUnitH0Pullback Y a = Sheaf.H.map t.hom 0 c :=
    Sheaf.H.map_comp_apply.{u} e.hom t.hom b
  have he : p ≫ (Scheme.Etale.mk (𝟙 X)).hom =
      (Scheme.Etale.mk (𝟙 Y.left)).hom ≫ p :=
    (Category.comp_id p).trans (Category.id_comp p).symm
  have hm : (MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      (A := (etalePostcompose p).obj (Scheme.Etale.mk (𝟙 Y.left)))
      (B := Scheme.Etale.mk (𝟙 X)) p he) =
      hX.from ((etalePostcompose p).obj (Scheme.Etale.mk (𝟙 Y.left))) :=
    hX.hom_ext _ _
  have hn : Sheaf.H.equiv₀.{u} C hY (Sheaf.H.map t.hom 0 c) =
      t.hom.hom.app (op (Scheme.Etale.mk (𝟙 Y.left)))
        (Sheaf.H.equiv₀.{u} B hY c) :=
    (Sheaf.H.equiv₀_naturality.{u} (J := Y.left.smallEtaleTopology)
      (F := B) (G := C) hY t.hom c).symm
  have hs : Sheaf.H.equiv₀.{u} B hY c =
      Q.obj.map (hX.from ((etalePostcompose p).obj (Scheme.Etale.mk (𝟙 Y.left)))).op
        (Sheaf.H.equiv₀.{u} Q hX a) :=
    (etaleAbelianRestrictionCohomologyPullback_zero_sections p Q hX hY p he a).trans
      (congrArg
        (fun z : (etalePostcompose p).obj (Scheme.Etale.mk (𝟙 Y.left)) ⟶
            Scheme.Etale.mk (𝟙 X) =>
          Q.obj.map z.op (Sheaf.H.equiv₀.{u} Q hX a)) hm)
  exact (congrArg (Sheaf.H.equiv₀.{u} C hY) hp).trans
    (hn.trans
      (congrArg
        (fun z : B.obj.obj (op (Scheme.Etale.mk (𝟙 Y.left))) =>
          t.hom.hom.app (op (Scheme.Etale.mk (𝟙 Y.left))) z) hs))

end EtaleCohomology
