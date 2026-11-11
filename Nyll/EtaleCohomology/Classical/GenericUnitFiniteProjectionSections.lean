/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteDeckSections
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteRestriction
public import Nyll.EtaleCohomology.Classical.GenericUnitRationalSections
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.SheafH0TerminalTransport
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The original generic-unit projection on a finite cover

The actual unit-section coordinate of the covering function field agrees
with the native H⁰ coordinate on that same scheme. The quotient comparison
therefore retains the original cokernel projection, including its original
function-field unit and native cohomology class.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups

namespace EtaleCohomology

variable {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
  (Y : FiniteEtale X) [IsConnected Y] [IsIntegral Y.left]

private theorem finiteGenericUnitPushforward_top
    (s : ((etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
      (etaleMultiplicativeGroupSheaf (Spec X.functionField))).obj.obj
        (op ((finiteEtaleInclusion X).obj Y))) :
    let GX := (etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
      (etaleMultiplicativeGroupSheaf (Spec X.functionField))
    let W := (zariskiToEtale Y.left).obj ⊤
    (etaleRestrictionFiniteGenericUnitPushforwardIso Y).hom.hom.app (op W)
        ((etaleRestrictionTopObjectSectionIso Y.hom GX).inv s) =
      rationalUnitDirectImageSection (Y.left.fromSpecStalk (genericPoint Y.left)) W
        (finiteEtaleGenericUnitSectionsEquiv Y s) := by
  intro GX W
  let jX := X.fromSpecStalk (genericPoint X)
  let jY := Y.left.fromSpecStalk (genericPoint Y.left)
  let g := Spec.map (CommRingCat.ofHom
    ((show Y.left ⟶ X from Y.hom).functionFieldMap
      (finiteEtale_hom_denseRange_of_isConnected Y)))
  have H : IsPullback jY g Y.hom jX := finiteEtaleGenericPointIsPullback Y
  have : Etale g := MorphismProperty.of_isPullback (P := @Etale) H Y.prop.toEtale
  let e := H.isoPullback
  let t := (etalePostcomposeTopObjectIso Y.hom).hom
  let k := ((etaleBaseChange jX).map t).left
  let H' := (IsPullback.of_hasPullback W.hom jY).paste_vert H
  let c := H'.isoPullback.hom
  have ht : t.left = W.hom := by
    change (zariskiToEtaleTopIso Y.left).hom.left ≫ 𝟙 Y.left = W.hom
    exact (zariskiToEtaleTopIso Y.left).hom.w
  have hk : k ≫ pullback.fst Y.hom jX =
      pullback.fst (W.hom ≫ Y.hom) jX ≫ W.hom := by
    have h : k ≫ pullback.fst Y.hom jX =
        pullback.fst (W.hom ≫ Y.hom) jX ≫ t.left := by
      dsimp only [k, etaleBaseChange]
      exact pullback.lift_fst _ _ _
    exact h.trans (congrArg (fun z => pullback.fst (W.hom ≫ Y.hom) jX ≫ z) ht)
  have hk' : k ≫ pullback.snd Y.hom jX =
      pullback.snd (W.hom ≫ Y.hom) jX := by
    dsimp only [k, etaleBaseChange]
    exact pullback.lift_snd _ _ _
  have hc : c ≫ k = pullback.snd W.hom jY ≫ e.hom := by
    apply pullback.hom_ext
    · calc
        (c ≫ k) ≫ pullback.fst Y.hom jX =
            c ≫ (k ≫ pullback.fst Y.hom jX) := Category.assoc _ _ _
        _ = c ≫ (pullback.fst (W.hom ≫ Y.hom) jX ≫ W.hom) :=
          congrArg (fun z : pullback (W.hom ≫ Y.hom) jX ⟶ Y.left => c ≫ z) hk
        _ = (c ≫ pullback.fst (W.hom ≫ Y.hom) jX) ≫ W.hom :=
          (Category.assoc _ _ _).symm
        _ = pullback.fst W.hom jY ≫ W.hom :=
          congrArg (fun z : pullback W.hom jY ⟶ W.left => z ≫ W.hom)
            H'.isoPullback_hom_fst
        _ = pullback.snd W.hom jY ≫ jY := pullback.condition
        _ = pullback.snd W.hom jY ≫ (e.hom ≫ pullback.fst Y.hom jX) :=
          congrArg (fun z : Spec Y.left.functionField ⟶ Y.left =>
            pullback.snd W.hom jY ≫ z) H.isoPullback_hom_fst.symm
        _ = (pullback.snd W.hom jY ≫ e.hom) ≫ pullback.fst Y.hom jX :=
          (Category.assoc _ _ _).symm
    · calc
        (c ≫ k) ≫ pullback.snd Y.hom jX =
            c ≫ (k ≫ pullback.snd Y.hom jX) := Category.assoc _ _ _
        _ = c ≫ pullback.snd (W.hom ≫ Y.hom) jX :=
          congrArg (fun z : pullback (W.hom ≫ Y.hom) jX ⟶ Spec X.functionField =>
            c ≫ z) hk'
        _ = pullback.snd W.hom jY ≫ g := H'.isoPullback_hom_snd
        _ = pullback.snd W.hom jY ≫ (e.hom ≫ pullback.snd Y.hom jX) :=
          congrArg (fun z : Spec Y.left.functionField ⟶ Spec X.functionField =>
            pullback.snd W.hom jY ≫ z) H.isoPullback_hom_snd.symm
        _ = (pullback.snd W.hom jY ≫ e.hom) ≫ pullback.snd Y.hom jX :=
          (Category.assoc _ _ _).symm
  let Γe := Scheme.ΓSpecIso (CommRingCat.of Y.left.functionField)
  have hr : k.appTop ≫ c.appTop =
      (e.hom.appTop ≫ Γe.hom) ≫ (Γe.inv ≫ (pullback.snd W.hom jY).appTop) := by
    have hcancel :
        (e.hom.appTop ≫ Γe.hom) ≫ (Γe.inv ≫ (pullback.snd W.hom jY).appTop) =
          e.hom.appTop ≫ (pullback.snd W.hom jY).appTop :=
      (Category.assoc _ _ _).trans
        (congrArg (fun z => e.hom.appTop ≫ z)
          (Γe.hom_inv_id_assoc (pullback.snd W.hom jY).appTop))
    exact (Scheme.Hom.comp_appTop c k).symm.trans
      ((congrArg (fun z : pullback W.hom jY ⟶ pullback Y.hom jX => z.appTop) hc).trans
        ((Scheme.Hom.comp_appTop (pullback.snd W.hom jY) e.hom).trans hcancel.symm))
  have hs := etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback_app
    Y.hom jX jY g H W (GX.obj.map t.op s)
  change (etaleRestrictionFiniteGenericUnitPushforwardIso Y).hom.hom.app (op W)
      (GX.obj.map t.op s) =
    Additive.ofMul (Units.map c.appTop.hom.toMonoidHom (GX.obj.map t.op s).toMul) at hs
  change (etaleRestrictionFiniteGenericUnitPushforwardIso Y).hom.hom.app (op W)
      (GX.obj.map t.op s) = _
  refine hs.trans ?_
  calc
    _ = rationalUnitDirectImageSection jY W
        (Additive.ofMul (Units.map ((e.hom.appTop ≫ Γe.hom).hom.toMonoidHom) s.toMul)) := by
      apply Additive.toMul.injective
      apply Units.ext
      exact ConcreteCategory.congr_hom hr s.toMul.val
    _ = _ := congrArg (rationalUnitDirectImageSection jY W)
      (finiteEtaleGenericUnitSectionsEquiv_apply Y s).symm

/-- The quotient section of an original unit is the original native
H⁰ projection of that same unit in the covering function field. -/
theorem finiteEtaleGenericUnitQuotientSectionsEquiv_projection
    (s : ((etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
      (etaleMultiplicativeGroupSheaf (Spec X.functionField))).obj.obj
        (op ((finiteEtaleInclusion X).obj Y))) :
    finiteEtaleGenericUnitQuotientSectionsEquiv Y
        ((etaleGenericUnitShortComplex X).g.hom.app
          (op ((finiteEtaleInclusion X).obj Y)) s) =
      Sheaf.H.map (etaleGenericUnitShortComplex Y.left).g 0
        ((genericPointUnitsH0Equiv Y.left).symm (finiteEtaleGenericUnitSectionsEquiv Y s)) := by
  let W := (zariskiToEtale Y.left).obj ⊤
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) Y.left
  let hW : IsTerminal W := hT.ofIso (zariskiToEtaleTopIso Y.left).symm
  let GX := (etaleGenericUnitShortComplex X).X₂
  let GY := (etaleGenericUnitShortComplex Y.left).X₂
  let QX := etaleGenericUnitQuotient X
  let QY := etaleGenericUnitQuotient Y.left
  let πX := (etaleGenericUnitShortComplex X).g
  let πY := (etaleGenericUnitShortComplex Y.left).g
  let a := (genericPointUnitsH0Equiv Y.left).symm (finiteEtaleGenericUnitSectionsEquiv Y s)
  have ha : Sheaf.H.equiv₀ GY hW a =
      rationalUnitDirectImageSection (Y.left.fromSpecStalk (genericPoint Y.left)) W
        (finiteEtaleGenericUnitSectionsEquiv Y s) := by
    exact (sheafH0_restriction GY hW hT (hT.from W) a).symm.trans
      ((genericPointUnitsH0Equiv_section Y.left a W).trans
        (congrArg
          (rationalUnitDirectImageSection (Y.left.fromSpecStalk (genericPoint Y.left)) W)
          ((genericPointUnitsH0Equiv Y.left).apply_symm_apply
            (finiteEtaleGenericUnitSectionsEquiv Y s))))
  have hnat : πX.hom.app (op ((etalePostcompose Y.hom).obj W))
      ((etaleRestrictionTopObjectSectionIso Y.hom GX).inv s) =
    (etaleRestrictionTopObjectSectionIso Y.hom QX).inv
      (πX.hom.app (op ((finiteEtaleInclusion X).obj Y)) s) :=
    ConcreteCategory.congr_hom
      (πX.hom.naturality (etalePostcomposeTopObjectIso Y.hom).hom.op) s
  have hπ := ConcreteCategory.congr_hom
    (congrArg (fun z => z.hom.app (op W)) (etaleRestrictionFiniteGenericUnitQuotientIso_π Y))
    ((etaleRestrictionTopObjectSectionIso Y.hom GX).inv s)
  change (etaleRestrictionFiniteGenericUnitQuotientIso Y).hom.hom.app (op W)
      (πX.hom.app (op ((etalePostcompose Y.hom).obj W))
        ((etaleRestrictionTopObjectSectionIso Y.hom GX).inv s)) =
    πY.hom.app (op W)
      ((etaleRestrictionFiniteGenericUnitPushforwardIso Y).hom.hom.app (op W)
        ((etaleRestrictionTopObjectSectionIso Y.hom GX).inv s)) at hπ
  have hprojection := hπ.trans
    (congrArg (πY.hom.app (op W)) (finiteGenericUnitPushforward_top Y s))
  apply (Sheaf.H.equiv₀ QY hW).injective
  exact (finiteEtaleGenericUnitQuotientSectionsEquiv_apply Y _).trans
    ((congrArg ((etaleRestrictionFiniteGenericUnitQuotientIso Y).hom.hom.app (op W))
      hnat.symm).trans
        (hprojection.trans
          ((congrArg (πY.hom.app (op W)) ha.symm).trans
            (Sheaf.H.equiv₀_naturality hW πY a))))

end EtaleCohomology
