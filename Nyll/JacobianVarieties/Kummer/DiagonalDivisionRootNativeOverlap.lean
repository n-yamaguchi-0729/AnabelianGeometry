/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.AlgebraicPoints
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProductIntegral
public import Nyll.AlgebraicCurves.Geometry.Picard.DivisionPullbackCocycle
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Kummer.CurveNativeH1Picard
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicIsomorphism
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.ExternalCupPullbackComposition
public import Nyll.EtaleCohomology.Classical.FiniteCechKernelCupRestriction
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechOverlap
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.InvertibleRootCechDescent
public import Nyll.EtaleCohomology.Classical.KummerRestriction
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.GaloisSections
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionBaseChangeDescent
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionDescentTransition
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionKummerTransition
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionNativeTransition
public import Nyll.ProCGroups.Abelian.FullTateModule
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Native overlap values of the retained diagonal root

The actual descent class of the retained division root is evaluated on
the canonical base change of each integral parameter overlap. The same
constant division difference supplies its native finite H¹ class. The
original product-cover isomorphism and the original coefficient maps
identify this value with its first-projection pullback, before any cup
or tensor comparison.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Opposite Abelian
open AlgebraicGeometry.RelPicard AlgebraicCurve NeronModelInfra GoodReductionJacobian
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F)
  (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
  (D : RelativePic0Designation K M.toBase)
  (hD : RepresentsRelSubPic M.toBase ε (algEquivZeroCut M.toBase ε) D)
  [Smooth D.toBase] [IsProper D.toBase]
  (aj : SchemeHomOver M.toBase D.toBase)

variable
  (hclass : ∀ x : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase,
    Nonempty ((hD.poincare.pullbackAlong
      ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
        ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
      (RelEffCartierDiv.ofPoint M.toBase x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint M.toBase ε.1 ε.2).idealModule))
  (e : Pic0 K F ≃+
    (hD.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase ε)).AlgPoints
      (hD.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut M.toBase ε)) K)
  (hpoint : ∀ x : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase,
    ∃ Dv : Divisor.degZero (K := K) (F := F),
      (Dv : Divisor K F) = Finsupp.single (M.pointEquivPlace x) 1 -
        Finsupp.single (M.pointEquivPlace ε) 1 ∧
      (RelativeGroupLaw.AlgPoints.toPoint (e (Pic0.mk Dv))).1 = x.1 ≫ aj.1)

local notation "𝒫" => algEquivZeroGroupCut M.toBase ε
local notation "G" => RepresentsRelSubPic.relativeGroupLaw (P := 𝒫) hD
local notation "hc" => RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := 𝒫) hD

include hclass hpoint in
/-- The original root-sensitive class has, on every actual parameter
overlap, the first-projection pullback of the native finite H¹ class
of the same constant torsion difference. The overlap source is the
canonical base-changed object used by the actual Cech kernel. -/
theorem divisionRootDescent_exists_nativePicard_overlap
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
    (τe : Pic0.torsion K F (ℓ ^ (n + 1)) ≃+
      ProCGroups.torsionLevel ((G).AlgPoints hc K)
        ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos (n + 1)⟩)
    (hτe : ∀ a, (τe a).val = e a.val)
    (B : FiniteEtale M.C) [IsIntegral B.left]
    (z : SchemeHomOver (B.hom ≫ M.toBase)
      (hD.divisionStructure (P := 𝒫) aj (ℓ ^ (n + 1))))
    (hz : postComp (hD.divisionBaseMap (P := 𝒫) aj (ℓ ^ (n + 1))) z =
      (⟨B.hom, rfl⟩ : SchemeHomOver (B.hom ≫ M.toBase) M.toBase))
    (W : FiniteEtale M.C) [IsIntegral W.left] (m₀ m₁ : W ⟶ B)
    {T : (pullback M.toBase M.toBase).Etale} (hT : IsTerminal T)
    (q : (etaleBaseChange (pullback.snd M.toBase M.toBase)).obj
      ((finiteEtaleInclusion M.C).obj B) ⟶ T) :
    let c := M.toBase
    let Y := pullback c c
    let N : ℕ+ := ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos (n + 1)⟩
    let hnK : IsUnit ((N : ℕ) : K) := by
      change IsUnit ((ℓ ^ (n + 1) : ℕ) : K)
      simpa only [Nat.cast_pow] using hℓ.pow (n + 1)
    let BC := etaleBaseChange (pullback.snd c c)
    let VB := BC.obj ((finiteEtaleInclusion M.C).obj B)
    let eB := diagonalParameterProductCoverBaseChangeIso c B
    let _ : IsIntegral (diagonalParameterProductCover c B).left :=
      isIntegral_pullback_of_smooth_of_isAlgClosed (X := M.C) (Y := B.left)
        c (show B.left ⟶ Spec (.of K) from B.hom ≫ c)
    let _ : IsIntegral VB.left := by
      have hIso : IsIso eB.hom.left := inferInstanceAs
        (IsIso ((Scheme.Etale.forget Y ⋙ Over.forget Y).map eB.hom))
      exact @IsIntegral.of_isIso (diagonalParameterProductCover c B).left VB.left
        (inferInstanceAs (IsIntegral (diagonalParameterProductCover c B).left))
        eB.hom.left hIso
    let A := abelianCechAugmentationSequence Y.smallEtaleTopology hT q
    let _ := (Scheme.Modules.pullback (baseChangeSnd c z)).obj
      (hD.divisionRootFamily (P := 𝒫) aj (N : ℕ)).L
    let hL := (hD.divisionRootFamily (P := 𝒫) aj (N : ℕ)).isInvertible.pullback
      (baseChangeSnd c z)
    let hLB := hL.pullback eB.inv.left
    let s : W.left ⟶ Spec (.of K) := W.hom ≫ c
    let x₀ : SchemeHomOver s (B.hom ≫ c) :=
      ⟨m₀.left, (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c) m₀.w)⟩
    let y₀ : SchemeHomOver s (B.hom ≫ c) :=
      ⟨m₁.left, (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c) m₁.w)⟩
    let x := postComp z x₀
    let y := postComp z y₀
    let v : SchemeHomOver s (𝟙 (Spec (.of K))) := ⟨s, Category.comp_id s⟩
    let WB := BC.obj ((finiteEtaleInclusion M.C).obj W)
    let u₀ := BC.map ((finiteEtaleInclusion M.C).map m₀)
    let u₁ := BC.map ((finiteEtaleInclusion M.C).map m₁)
    let lB := pullback.lift u₀ u₁ (hT.hom_ext (u₀ ≫ q) (u₁ ≫ q))
    let edgeB := (freeAbelianSheafYoneda Y.smallEtaleTopology).map lB ≫
      (freeCechEdgeSheafIso Y.smallEtaleTopology q).inv ≫
        abelianCechFirstRelationMap Y.smallEtaleTopology hT q
    ∀ a : Ext.{u} A.X₁ (etaleRootsOfUnitySheaf Y (N : ℕ)) 1,
      a.comp (Ext.mk₀ (kernel.ι (etaleMultiplicativeGroupPower Y (N : ℕ)))) (add_zero 1) =
        (Ext.mk₀ A.f).comp (invertibleModuleCohomologyPresheafH1 VB hLB) (zero_add 1) →
      let aF := a.comp
        (Ext.mk₀ (ellPowerConstantKummerKernelIso (pullback.snd c c ≫ c) ℓ hℓ n).inv)
          (add_zero 1)
      ∃ t : ProCGroups.torsionLevel ((G).AlgPoints hc K) N,
        postComp (RelativeGroupLaw.UnitMultiplication.torsionPointSection G hc ⟨N, hnK⟩ t) v =
            hD.divisionDifference (P := 𝒫) aj (N : ℕ) x y ∧
          finiteLevelCohomologyPresheafRestriction Y ℓ n WB 1
              ((Ext.mk₀ edgeB).comp aF (zero_add 1)) =
            finiteLevelCohomologyPullback ℓ (WB.hom ≫ pullback.fst c c) n 1
              ((M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n).symm (τe.symm t)) := by
  intro c Y N hnK BC VB eB hU hVB A L hL hLB s x₀ y₀ x y v WB u₀ u₁ lB edgeB a hcoeff aF
  have hxy : postComp (hD.divisionBaseMap (P := 𝒫) aj (N : ℕ)) x =
      postComp (hD.divisionBaseMap (P := 𝒫) aj (N : ℕ)) y :=
    hD.parameterOverlapMaps_division_projection_eq (P := 𝒫)
      aj (N : ℕ) B z hz W m₀ m₁
  have hUW : IsIntegral (diagonalParameterProductCover c W).left :=
    isIntegral_pullback_of_smooth_of_isAlgClosed (X := M.C) (Y := W.left) c s
  obtain ⟨t, hconstant, htransition⟩ :=
    M.divisionTransitionFiniteClass_exists_nativePicard ε D hD aj hclass e hpoint
      ℓ hℓ n τe hτe (W := W.left) s x y hxy
  refine ⟨t, hconstant, ?_⟩
  let UW := (finiteEtaleInclusion Y).obj (diagonalParameterProductCover c W)
  let eW := diagonalParameterProductCoverBaseChangeIso c W
  have : IsIso eW.hom.left := inferInstanceAs
    (IsIso ((Scheme.Etale.forget Y ⋙ Over.forget Y).map eW.hom))
  have : IsIntegral (pullback M.toBase s) := hUW
  let P := freeAbelianSheafYoneda Y.smallEtaleTopology
  let r₀ := diagonalParameterProductCoverMap c m₀
  let r₁ := diagonalParameterProductCoverMap c m₁
  let l := pullback.lift (r₀ ≫ eB.hom) (r₁ ≫ eB.hom)
    (hT.hom_ext ((r₀ ≫ eB.hom) ≫ q) ((r₁ ≫ eB.hom) ≫ q))
  let edge := P.map l ≫ (freeCechEdgeSheafIso Y.smallEtaleTopology q).inv ≫
    abelianCechFirstRelationMap Y.smallEtaleTopology hT q
  have hl : eW.hom ≫ lB = l := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact diagonalParameterProductCoverBaseChangeIso_naturality c m₀
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact diagonalParameterProductCoverBaseChangeIso_naturality c m₁
  have hedge : P.map eW.hom ≫ edgeB = edge := by
    change P.map eW.hom ≫ (P.map lB ≫
      (freeCechEdgeSheafIso Y.smallEtaleTopology q).inv ≫
        abelianCechFirstRelationMap Y.smallEtaleTopology hT q) = edge
    rw [← Category.assoc, ← Functor.map_comp, hl]
  let Fₙ := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
    (ellPowerCoefficients.{u} ℓ n)
  let dY : Y ⟶ Spec (.of K) := pullback.snd c c ≫ c
  let eμ : Fₙ ≅ etaleRootsOfUnitySheaf Y (N : ℕ) :=
    ellPowerConstantKummerKernelIso dY ℓ hℓ n
  let b : Sheaf.H'.{u} Fₙ 1 WB := (Ext.mk₀ edgeB).comp aF (zero_add 1)
  have ha : aF.comp (Ext.mk₀ eμ.hom) (add_zero 1) = a := by
    change (a.comp (Ext.mk₀ eμ.inv) (add_zero 1)).comp
      (Ext.mk₀ eμ.hom) (add_zero 1) = a
    have hinv : (Ext.mk₀.{u} eμ.inv).comp (Ext.mk₀ eμ.hom) (zero_add 0) =
        Ext.mk₀ (𝟙 (etaleRootsOfUnitySheaf Y (N : ℕ))) :=
      (Ext.mk₀_comp_mk₀ eμ.inv eμ.hom).trans
        (congrArg (fun f : etaleRootsOfUnitySheaf Y (N : ℕ) ⟶
          etaleRootsOfUnitySheaf Y (N : ℕ) => Ext.mk₀.{u} f) eμ.inv_hom_id)
    exact (Ext.comp_assoc_of_second_deg_zero a (Ext.mk₀ eμ.inv)
      (Ext.mk₀ eμ.hom) (add_zero 1)).trans
      ((congrArg (fun f : Ext.{u} (etaleRootsOfUnitySheaf Y (N : ℕ))
        (etaleRootsOfUnitySheaf Y (N : ℕ)) 0 => a.comp f (add_zero 1)) hinv).trans
        (Ext.comp_mk₀_id a))
  have hcoef :
      (((Sheaf.cohomologyPresheafFunctor Y.smallEtaleTopology 1).map eμ.hom).app
        (op UW)) ((Fₙ.cohomologyPresheaf 1).map eW.hom.op b) =
      (Ext.mk₀ edge).comp a (zero_add 1) := by
    change ((Ext.mk₀ (P.map eW.hom)).comp
      ((Ext.mk₀ edgeB).comp aF (zero_add 1)) (zero_add 1)).comp
        (Ext.mk₀ eμ.hom) (add_zero 1) = _
    have he := (Ext.mk₀_comp_mk₀_assoc (P.map eW.hom) edgeB aF).trans
      (congrArg (fun f : P.obj UW ⟶ A.X₁ =>
        (Ext.mk₀ f).comp aF (zero_add 1)) hedge)
    exact (congrArg (fun z : Ext.{u} (P.obj UW) Fₙ 1 =>
      z.comp (Ext.mk₀ eμ.hom) (add_zero 1)) he).trans
      ((Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ edge) aF
        (Ext.mk₀ eμ.hom) (zero_add 1)).trans
        (congrArg (fun z : Ext.{u} A.X₁ (etaleRootsOfUnitySheaf Y (N : ℕ)) 1 =>
          (Ext.mk₀ edge).comp z (zero_add 1)) ha))
  have hbase : UW.hom ≫ dY = pullback.snd c s ≫ s := by
    change baseChangeSnd c (⟨W.hom, rfl⟩ : SchemeHomOver (W.hom ≫ c) c) ≫
      (pullback.snd c c ≫ c) = pullback.snd c s ≫ s
    have hsnd : baseChangeSnd c
        (⟨W.hom, rfl⟩ : SchemeHomOver (W.hom ≫ c) c) ≫ pullback.snd c c =
          pullback.snd c s ≫ W.hom := pullback.lift_snd _ _ _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ c) hsnd).trans (Category.assoc _ _ _))
  have hroot : finiteLevelCohomologyPullback ℓ eW.hom.left n 1
      (finiteLevelCohomologyPresheafRestriction Y ℓ n WB 1 b) =
        hD.divisionTransitionFiniteClass (P := 𝒫) aj ℓ hℓ n x y hxy := by
    rw [← finiteLevelCohomologyPresheafRestriction_object_restriction
      Y ℓ n dY hℓ eW.hom 1 b]
    apply (finiteLevelKummerCohomologyEquiv (UW.hom ≫ dY) ℓ hℓ n 1).injective
    have hrestriction := finiteLevelCohomologyPresheafRestriction_kummer
      Y ℓ n dY hℓ UW 1 ((Fₙ.cohomologyPresheaf 1).map eW.hom.op b)
    have hcoefficient := congrArg
      (etaleRootsOfUnityCohomologyPresheafRestriction (N : ℕ) UW 1) hcoef
    have hdescent := hD.divisionRootDescent_overlap_maps_of_iso (P := 𝒫)
      aj (N : ℕ) B z hz W m₀ m₁ N.pos hnK eB hT q a hcoeff
    have hfinite : finiteLevelKummerCohomologyEquiv (pullback.snd c s ≫ s) ℓ hℓ n 1
        (hD.divisionTransitionFiniteClass (P := 𝒫) aj ℓ hℓ n x y hxy) =
      hD.divisionTransitionKummerClass (P := 𝒫) aj (N : ℕ) N.pos hnK x y hxy := by
      unfold RepresentsRelSubPic.divisionTransitionFiniteClass
      exact (finiteLevelKummerCohomologyEquiv (pullback.snd c s ≫ s) ℓ hℓ n 1).apply_symm_apply _
    have hbaseClass := congrArg
      (fun d : UW.left ⟶ Spec (.of K) => finiteLevelKummerCohomologyEquiv d ℓ hℓ n 1
        (hD.divisionTransitionFiniteClass (P := 𝒫) aj ℓ hℓ n x y hxy)) hbase
    exact hrestriction.trans
      (hcoefficient.trans (hdescent.trans (hfinite.symm.trans hbaseClass.symm)))
  have hfirst : eW.hom.left ≫ (WB.hom ≫ pullback.fst c c) = pullback.fst c s := by
    have hw : eW.hom.left ≫ WB.hom = UW.hom := eW.hom.w
    have hfst : UW.hom ≫ pullback.fst c c = pullback.fst c s :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ pullback.fst c c) hw).trans hfst)
  apply (finiteLevelCohomologyIso ℓ (asIso eW.hom.left) n 1).injective
  change finiteLevelCohomologyPullback ℓ eW.hom.left n 1
      (finiteLevelCohomologyPresheafRestriction Y ℓ n WB 1 b) =
    finiteLevelCohomologyPullback ℓ eW.hom.left n 1
      (finiteLevelCohomologyPullback ℓ (WB.hom ≫ pullback.fst c c) n 1
        ((M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n).symm (τe.symm t)))
  have hcomp := LinearMap.congr_fun
    (finiteLevelCohomologyPullback_comp eW.hom.left (WB.hom ≫ pullback.fst c c) ℓ n 1)
    ((M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n).symm (τe.symm t))
  have hfirstPull := congrArg
    (fun f : UW.left ⟶ M.C => finiteLevelCohomologyPullback ℓ f n 1
      ((M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n).symm (τe.symm t))) hfirst
  exact hroot.trans (htransition.trans (hfirstPull.symm.trans hcomp))

end AlgebraicCurve.CurveModel
