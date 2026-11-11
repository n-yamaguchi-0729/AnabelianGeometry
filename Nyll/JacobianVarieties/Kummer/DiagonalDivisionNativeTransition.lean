/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Designation
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.AlgebraicPoints
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProductIntegral
public import Nyll.AlgebraicCurves.Geometry.Picard.DivisionPullbackCocycle
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Kummer.CurveNativeH1Picard
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.RootsOfUnityPullbackComposition
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitMonodromy
public import Nyll.JacobianVarieties.Kummer.CurvePoincareNativePicard
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionConstantTransition
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionKummerTransition
public import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Native finite coordinates of the actual division transition

The actual constant torsion difference and its original Poincaré Kummer
class give one torsion point in the retained Picard coordinates. The
original transition on the parameter product is exactly the pullback
of that native finite H¹ class. Both the point and the cohomology class
are retained for the original overlap cup computation.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian EtaleCohomology
open EtaleCohomology.Classical

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F)
  (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
  (D : GoodReductionJacobian.RelativePic0Designation K M.toBase)
  (hD : RelPicard.RepresentsRelSubPic M.toBase ε
    (RelPicard.algEquivZeroCut M.toBase ε) D)
  [Smooth D.toBase] [IsProper D.toBase]
  (aj : SchemeHomOver M.toBase D.toBase)

local instance : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase

variable
    (hclass : ∀ x : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase,
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M.toBase ε.1 ε.2).idealModule))
    (e : Pic0 K F ≃+
      (hD.relativeGroupLaw (P := RelPicard.algEquivZeroGroupCut M.toBase ε)).AlgPoints
        (hD.relativeGroupLaw_isCommutative
          (P := RelPicard.algEquivZeroGroupCut M.toBase ε)) K)
    (hpoint : ∀ x : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase,
      ∃ Dv : Divisor.degZero (K := K) (F := F),
        (Dv : Divisor K F) = Finsupp.single (M.pointEquivPlace x) 1 -
          Finsupp.single (M.pointEquivPlace ε) 1 ∧
        (RelativeGroupLaw.AlgPoints.toPoint (e (Pic0.mk Dv))).1 = x.1 ≫ aj.1)

local notation "G" => RelPicard.RepresentsRelSubPic.relativeGroupLaw
  (P := RelPicard.algEquivZeroGroupCut M.toBase ε) hD
local notation "hc" => RelPicard.RepresentsRelSubPic.relativeGroupLaw_isCommutative
  (P := RelPicard.algEquivZeroGroupCut M.toBase ε) hD

include hclass hpoint in
/-- The same actual transition is the first-projection pullback of the
native finite H¹ class of its actual constant torsion difference. -/
theorem divisionTransitionFiniteClass_exists_nativePicard
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
    (τe : Pic0.torsion K F (ℓ ^ (n + 1)) ≃+
      ProCGroups.torsionLevel ((G).AlgPoints hc K)
        ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos (n + 1)⟩)
    (hτe : ∀ a, (τe a).val = e a.val)
    {W : Scheme.{u}} [IsIntegral W] (w : W ⟶ Spec (.of K)) [IsProper w]
    (x y : SchemeHomOver w (hD.divisionStructure
      (P := RelPicard.algEquivZeroGroupCut M.toBase ε) aj (ℓ ^ (n + 1))))
    (hxy : postComp (hD.divisionBaseMap
        (P := RelPicard.algEquivZeroGroupCut M.toBase ε) aj (ℓ ^ (n + 1))) x =
      postComp (hD.divisionBaseMap
        (P := RelPicard.algEquivZeroGroupCut M.toBase ε) aj (ℓ ^ (n + 1))) y) :
    let N : ℕ+ := ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos (n + 1)⟩
    let hnK : IsUnit ((N : ℕ) : K) := by
      change IsUnit ((ℓ ^ (n + 1) : ℕ) : K)
      simpa only [Nat.cast_pow] using hℓ.pow (n + 1)
    let _ : IsIntegral (pullback M.toBase w) :=
      isIntegral_pullback_of_smooth_of_isAlgClosed M.toBase w
    let v : SchemeHomOver w (𝟙 (Spec (.of K))) := ⟨w, Category.comp_id w⟩
    ∃ t : ProCGroups.torsionLevel ((G).AlgPoints hc K) N,
      postComp (RelativeGroupLaw.UnitMultiplication.torsionPointSection G hc ⟨N, hnK⟩ t) v =
          hD.divisionDifference (P := RelPicard.algEquivZeroGroupCut M.toBase ε)
            aj (N : ℕ) x y ∧
        hD.divisionTransitionFiniteClass (P := RelPicard.algEquivZeroGroupCut M.toBase ε)
            aj ℓ hℓ n x y hxy =
          finiteLevelCohomologyPullback ℓ (pullback.fst M.toBase w) n 1
            ((M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n).symm (τe.symm t)) := by
  intro N hnK hY v
  let C₀ := pullback M.toBase (𝟙 (Spec (.of K)))
  have : IsIntegral C₀ := isIntegral_pullback_of_smooth_of_isAlgClosed M.toBase (𝟙 _)
  let q₀ := inv (pullback.fst M.toBase (𝟙 (Spec (.of K))))
  let q := RelPicard.baseChangeSnd M.toBase v
  obtain ⟨τ, hτ, hconstant, _, κ, hκ, hpull⟩ :=
    hD.divisionTransitionKummerClass_exists_constant
      (P := RelPicard.algEquivZeroGroupCut M.toBase ε) aj (N : ℕ) w N.pos hnK x y hxy
  let s := Spec.map (CommRingCat.ofHom (algebraMap K K))
  have hs : s = 𝟙 (Spec (.of K)) := by
    change Spec.map (CommRingCat.ofHom (RingHom.id K)) = _
    rw [CommRingCat.ofHom_id]
    exact Spec.map_id (CommRingCat.of K)
  let p : SchemeHomOver s D.toBase :=
    schemeHomOverComp (𝟙 _) ((Category.comp_id _).trans hs.symm) τ
  have hp : (G).IsTorsionPoint s (N : ℕ) p :=
    (G).isTorsionPoint_schemeHomOverComp (𝟙 _) s (𝟙 _)
      ((Category.comp_id _).trans hs.symm) (N : ℕ) hτ
  let t : ProCGroups.torsionLevel ((G).AlgPoints hc K) N :=
    ⟨RelativeGroupLaw.AlgPoints.ofPoint p,
      (RelativeGroupLaw.AlgPoints.nsmul_eq_zero_iff (N : ℕ)
        (RelativeGroupLaw.AlgPoints.ofPoint p : (G).AlgPoints hc K)).mpr hp⟩
  have ht : RelativeGroupLaw.UnitMultiplication.torsionPointSection G hc ⟨N, hnK⟩ t = τ := by
    apply Subtype.ext
    exact Category.id_comp τ.1
  refine ⟨t, by rw [ht]; exact hconstant, ?_⟩
  have he : e (τe.symm t).val = t.val :=
    (hτe (τe.symm t)).symm.trans (congrArg Subtype.val (τe.apply_symm_apply t))
  have hpointτ : (RelativeGroupLaw.AlgPoints.toPoint (e (τe.symm t).val)).1 = τ.1 := by
    rw [he]
    exact Category.id_comp τ.1
  let b := (finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 1).symm
    (etaleRootsOfUnityCohomologyPullback q₀ (N : ℕ) 1 κ)
  have hb : b = (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n).symm (τe.symm t) := by
    apply (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n).injective
    rw [AddEquiv.apply_symm_apply]
    exact M.poincare_nativeFiniteLevel_of_abelJacobi ε D hD aj hclass e hpoint
      ℓ hℓ n (τe.symm t) τ hpointτ κ hκ
  have hκ₀ : finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 1
      ((M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n).symm (τe.symm t)) =
        etaleRootsOfUnityCohomologyPullback q₀ (N : ℕ) 1 κ := by
    rw [← hb]
    exact (finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 1).apply_symm_apply _
  have hq : q = pullback.fst M.toBase w ≫ q₀ := by
    apply (cancel_mono (pullback.fst M.toBase (𝟙 (Spec (.of K))))).mp
    have hright : (pullback.fst M.toBase w ≫ q₀) ≫
        pullback.fst M.toBase (𝟙 (Spec (.of K))) = pullback.fst M.toBase w := by
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact (RelPicard.BaseChange.baseChangeSnd_fst'
      (R' := K) (cc := M.toBase) (ψ := v)).trans hright.symm
  let d := pullback.snd M.toBase w ≫ w
  unfold RelPicard.RepresentsRelSubPic.divisionTransitionFiniteClass
  apply (finiteLevelKummerCohomologyEquiv d ℓ hℓ n 1).injective
  rw [AddEquiv.apply_symm_apply]
  have hfinite := finiteLevelKummerCohomologyEquiv_pullback
    (pullback.fst M.toBase w) M.toBase ℓ hℓ n 1
    ((M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n).symm (τe.symm t))
  rw [pullback.condition] at hfinite
  have hκpull := congrArg
    (etaleRootsOfUnityCohomologyPullback (pullback.fst M.toBase w) (N : ℕ) 1) hκ₀
  have hcomp := etaleRootsOfUnityCohomologyPullback_comp
    (pullback.fst M.toBase w) q₀ (pullback.snd M.toBase (𝟙 (Spec (.of K)))) N.pos hnK 1 κ
  have hqpull := congrArg
    (fun p : pullback M.toBase w ⟶ C₀ =>
      etaleRootsOfUnityCohomologyPullback p (N : ℕ) 1 κ) hq
  exact hpull.symm.trans (hqpull.trans (hcomp.trans (hκpull.symm.trans hfinite.symm)))

end AlgebraicCurve.CurveModel
