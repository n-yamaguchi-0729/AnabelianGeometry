/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianRestrictionPullback
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteRestriction
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteSections
public import Nyll.EtaleCohomology.Classical.GenericUnitOpenCohomology
public import Nyll.EtaleCohomology.Classical.GenericUnitOpenRestriction
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.SheafH0TerminalTransport
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Arbitrary generic-unit quotient sections and deck pullback

Sections on the original finite étale object identify with the original
native H⁰ of its own generic-unit quotient. Pasting the actual generic-point
squares proves equivariance for deck transformations. No global rational
representative of the quotient section is required.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups

namespace EtaleCohomology

variable {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
  (Y : FiniteEtale X) [IsConnected Y] [IsIntegral Y.left]

/-- The original quotient section at the actual finite cover is
the native H⁰ class on that same covering scheme. -/
def finiteEtaleGenericUnitQuotientSectionsEquiv :
    (etaleGenericUnitQuotient X).obj.obj (op ((finiteEtaleInclusion X).obj Y)) ≃+
      Sheaf.H.{u} (etaleGenericUnitQuotient Y.left) 0 := by
  let W := (zariskiToEtale Y.left).obj ⊤
  let hW : IsTerminal W :=
    (MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) Y.left).ofIso
        (zariskiToEtaleTopIso Y.left).symm
  let c := (etaleRestrictionTopObjectSectionIso Y.hom (etaleGenericUnitQuotient X)).symm ≪≫
    ((sheafToPresheaf Y.left.smallEtaleTopology AddCommGrpCat.{u}).mapIso
      (etaleRestrictionFiniteGenericUnitQuotientIso Y)).app (op W)
  exact c.addCommGroupIsoToAddEquiv.trans
    (Sheaf.H.equiv₀ (etaleGenericUnitQuotient Y.left) hW).symm

/-- Evaluation retains the original quotient restriction and its
actual component at the top-open object. -/
theorem finiteEtaleGenericUnitQuotientSectionsEquiv_apply
    (s : (etaleGenericUnitQuotient X).obj.obj (op ((finiteEtaleInclusion X).obj Y))) :
    let W := (zariskiToEtale Y.left).obj ⊤
    let hW : IsTerminal W :=
      (MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) Y.left).ofIso
          (zariskiToEtaleTopIso Y.left).symm
    Sheaf.H.equiv₀ (etaleGenericUnitQuotient Y.left) hW
        (finiteEtaleGenericUnitQuotientSectionsEquiv Y s) =
      (etaleRestrictionFiniteGenericUnitQuotientIso Y).hom.hom.app (op W)
        ((etaleRestrictionTopObjectSectionIso Y.hom (etaleGenericUnitQuotient X)).inv s) := by
  intro W hW
  exact (Sheaf.H.equiv₀ (etaleGenericUnitQuotient Y.left) hW).apply_symm_apply _

/-- Forgetting an actual deck automorphism gives a scheme isomorphism. -/
local instance finiteEtaleDeck_isIso_left (σ : Aut Y) : IsIso σ.asIso.hom.left :=
  (FiniteEtale.forget X ⋙ Over.forget X).map_isIso σ.asIso.hom

/-- Deck restriction of any original quotient section is exactly
the native generic-unit quotient pullback on its own covering scheme. -/
theorem finiteEtaleGenericUnitQuotientSectionsEquiv_deck (σ : Aut Y)
    (s : (etaleGenericUnitQuotient X).obj.obj (op ((finiteEtaleInclusion X).obj Y))) :
    finiteEtaleGenericUnitQuotientSectionsEquiv Y
        ((etaleGenericUnitQuotient X).obj.map ((finiteEtaleInclusion X).map σ.asIso.hom).op s) =
      etaleGenericUnitQuotientCohomologyPullback σ.asIso.hom.left 0
        (finiteEtaleGenericUnitQuotientSectionsEquiv Y s) := by
  let W := (zariskiToEtale Y.left).obj ⊤
  let hW : IsTerminal W :=
    (MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) Y.left).ofIso
        (zariskiToEtaleTopIso Y.left).symm
  let QX := etaleGenericUnitQuotient X
  let QY := etaleGenericUnitQuotient Y.left
  let g := Spec.map (CommRingCat.ofHom
    ((show Y.left ⟶ X from Y.hom).functionFieldMap
      (finiteEtale_hom_denseRange_of_isConnected Y)))
  have H : IsPullback (Y.left.fromSpecStalk (genericPoint Y.left)) g
      Y.hom (X.fromSpecStalk (genericPoint X)) := finiteEtaleGenericPointIsPullback Y
  have : Etale g := MorphismProperty.of_isPullback (P := @Etale) H Y.prop.toEtale
  have hg : (genericPointOpenIso σ.asIso.hom.left).hom ≫ g = g := by
    apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
    let a : Spec Y.left.functionField ⟶ Spec Y.left.functionField :=
      (genericPointOpenIso σ.asIso.hom.left).hom
    let j : Spec Y.left.functionField ⟶ Y.left :=
      Y.left.fromSpecStalk (genericPoint Y.left)
    have hdeck : σ.asIso.hom.left ≫ Y.hom = Y.hom := σ.asIso.hom.w
    calc
      (a ≫ g) ≫ X.fromSpecStalk (genericPoint X) =
          a ≫ (g ≫ X.fromSpecStalk (genericPoint X)) := Category.assoc _ _ _
      _ = a ≫ (j ≫ Y.hom) := congrArg (fun r => a ≫ r) H.w.symm
      _ = (a ≫ j) ≫ Y.hom := (Category.assoc _ _ _).symm
      _ = (j ≫ σ.asIso.hom.left) ≫ Y.hom :=
        congrArg (fun r : Spec Y.left.functionField ⟶ Y.left => r ≫ Y.hom)
          (genericPointOpenIsPullback σ.asIso.hom.left).w.symm
      _ = j ≫ (σ.asIso.hom.left ≫ Y.hom) := Category.assoc _ _ _
      _ = j ≫ Y.hom := congrArg (fun r => j ≫ r) hdeck
      _ = g ≫ X.fromSpecStalk (genericPoint X) := H.w
  let t : (etalePostcompose σ.asIso.hom.left).obj W ⟶ W :=
    (show (etalePostcompose σ.asIso.hom.left).obj W ⟶ Scheme.Etale.mk (𝟙 Y.left) from
      MorphismProperty.Over.homMk ((etalePostcompose σ.asIso.hom.left).obj W).hom
        (Category.comp_id _)) ≫ (zariskiToEtaleTopIso Y.left).inv
  have ht : t.left ≫ W.hom = W.hom ≫ σ.asIso.hom.left := t.w
  have htm : (MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      (A := (etalePostcompose σ.asIso.hom.left).obj W) (B := W) t.left ht) = t := by
    apply MorphismProperty.Over.Hom.ext
    rfl
  have hp := ConcreteCategory.congr_hom
    (etaleRestrictionUnitQuotient_sections_tower_eq Y.hom σ.asIso.hom.left
      (X.fromSpecStalk (genericPoint X))
      (Y.left.fromSpecStalk (genericPoint Y.left)) g
      (Y.left.fromSpecStalk (genericPoint Y.left)) (genericPointOpenIso σ.asIso.hom.left).hom
      H (genericPointOpenIsPullback σ.asIso.hom.left) Y.hom g σ.asIso.hom.w hg H) s
  let a := finiteEtaleGenericUnitQuotientSectionsEquiv Y s
  let e := etaleRestrictionGenericUnitQuotientIso σ.asIso.hom.left
  have hr : Sheaf.H.equiv₀
        ((etaleRestriction σ.asIso.hom.left AddCommGrpCat.{u}).obj QY) hW
        (etaleAbelianRestrictionCohomologyPullback σ.asIso.hom.left QY 0 a) =
      QY.obj.map t.op (Sheaf.H.equiv₀ QY hW a) :=
    (etaleAbelianRestrictionCohomologyPullback_zero_sections
      σ.asIso.hom.left QY hW hW t.left ht a).trans
        (congrArg (fun m : (etalePostcompose σ.asIso.hom.left).obj W ⟶ W =>
          QY.obj.map m.op (Sheaf.H.equiv₀ QY hW a)) htm)
  have hright : Sheaf.H.equiv₀ QY hW
        (etaleGenericUnitQuotientCohomologyPullback σ.asIso.hom.left 0 a) =
      e.hom.hom.app (op W) (QY.obj.map t.op
        ((etaleRestrictionFiniteGenericUnitQuotientIso Y).hom.hom.app (op W)
          ((etaleRestrictionTopObjectSectionIso Y.hom QX).inv s))) :=
    (congrArg (Sheaf.H.equiv₀ QY hW)
      (etaleGenericUnitQuotientCohomologyPullback_restriction σ.asIso.hom.left 0 a)).trans
        ((Sheaf.H.equiv₀_naturality hW e.hom _).symm.trans
          (congrArg (e.hom.hom.app (op W))
            (hr.trans (congrArg (QY.obj.map t.op)
              (finiteEtaleGenericUnitQuotientSectionsEquiv_apply Y s)))))
  apply (Sheaf.H.equiv₀ QY hW).injective
  refine (finiteEtaleGenericUnitQuotientSectionsEquiv_apply Y _).trans ?_
  refine Eq.trans ?_ hright.symm
  change
    (etaleRestrictionFiniteGenericUnitQuotientIso Y).hom.hom.app (op W)
        (QX.obj.map (etalePostcomposeTopObjectIso Y.hom).hom.op
          (QX.obj.map ((finiteEtaleInclusion X).map σ.asIso.hom).op s)) =
      e.hom.hom.app (op W) (QY.obj.map t.op
        ((etaleRestrictionFiniteGenericUnitQuotientIso Y).hom.hom.app (op W)
          (QX.obj.map (etalePostcomposeTopObjectIso Y.hom).hom.op s))) at hp
  rw [etaleRestrictionTopObjectSectionIso_inv]
  exact hp

/-- A class restricted from the original base is sent to its actual
native finite-cover pullback by this same section equivalence. -/
theorem finiteEtaleGenericUnitQuotientSectionsEquiv_global
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0) :
    let hX := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    finiteEtaleGenericUnitQuotientSectionsEquiv Y
        ((etaleGenericUnitQuotient X).obj.map
          (hX.from ((finiteEtaleInclusion X).obj Y)).op
          (Sheaf.H.equiv₀ (etaleGenericUnitQuotient X) hX a)) =
      finiteGenericUnitH0Pullback Y a := by
  intro hX
  let W := (zariskiToEtale Y.left).obj ⊤
  let hY := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) Y.left
  let hW : IsTerminal W := hY.ofIso (zariskiToEtaleTopIso Y.left).symm
  let QX := etaleGenericUnitQuotient X
  let QY := etaleGenericUnitQuotient Y.left
  have hm : (etalePostcomposeTopObjectIso Y.hom).hom ≫
      hX.from ((finiteEtaleInclusion X).obj Y) =
      hX.from ((etalePostcompose Y.hom).obj W) := hX.hom_ext _ _
  have hcomp :
      QX.obj.map (hX.from ((finiteEtaleInclusion X).obj Y)).op ≫
          QX.obj.map (etalePostcomposeTopObjectIso Y.hom).hom.op =
        QX.obj.map (hX.from ((etalePostcompose Y.hom).obj W)).op :=
    (QX.obj.map_comp (hX.from ((finiteEtaleInclusion X).obj Y)).op
      (etalePostcomposeTopObjectIso Y.hom).hom.op).symm.trans
        (congrArg (fun z : (etalePostcompose Y.hom).obj W ⟶ Scheme.Etale.mk (𝟙 X) =>
          QX.obj.map z.op) hm)
  have hh := ConcreteCategory.congr_hom hcomp (Sheaf.H.equiv₀ QX hX a)
  have hglobal := (sheafH0_restriction QY hW hY (hY.from W)
    (finiteGenericUnitH0Pullback Y a)).symm.trans
      ((congrArg (QY.obj.map (hY.from W).op)
        (finiteGenericUnitH0Pullback_sections Y a)).trans
          (finiteGenericUnitGlobalSectionsMap_restrict Y W (Sheaf.H.equiv₀ QX hX a)))
  apply (Sheaf.H.equiv₀ QY hW).injective
  refine (finiteEtaleGenericUnitQuotientSectionsEquiv_apply Y _).trans ?_
  refine Eq.trans ?_ hglobal.symm
  apply congrArg ((etaleRestrictionFiniteGenericUnitQuotientIso Y).hom.hom.app (op W))
  exact (ConcreteCategory.congr_hom
    (etaleRestrictionTopObjectSectionIso_inv Y.hom QX)
      (QX.obj.map (hX.from ((finiteEtaleInclusion X).obj Y)).op
        (Sheaf.H.equiv₀ QX hX a))).trans hh

end EtaleCohomology
