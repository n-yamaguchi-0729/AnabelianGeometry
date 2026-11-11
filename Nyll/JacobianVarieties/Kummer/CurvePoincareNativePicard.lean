/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgEquivZeroGroupCut
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Designation
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardDegree
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardZero
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProductIntegral
public import Nyll.AlgebraicCurves.Geometry.Schemes.BaseChange.HomPullbackKerPowInvModuleIso
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Divisors.CartierPointSums
public import Nyll.AlgebraicCurves.Models.Divisors.CurveCartierDivisorCoordinates
public import Nyll.AlgebraicCurves.Models.Divisors.CurveNativePicard
public import Nyll.AlgebraicCurves.Models.Kummer.CurveNativeH1Picard
public import Nyll.AlgebraicCurves.Places.Degree.DegEqOneAlgClosed
public import Nyll.EtaleCohomology.Classical.CartierCyclePullback
public import Nyll.EtaleCohomology.Classical.DiagonalPointSectionIdeals
public import Nyll.EtaleCohomology.Classical.GraphCartierCycleClass
public import Nyll.EtaleCohomology.Classical.InvertibleCartierComparison
public import Nyll.EtaleCohomology.Classical.KummerH1Functoriality
public import Nyll.JacobianVarieties.Kummer.PoincareNativeClass
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The native Picard class of the same Poincaré fibre

The actual Poincaré family gives an additive native H¹(Gm) class. Its
Abel--Jacobi point formula identifies this class on point differences.
Those differences generate Pic⁰, so the same identification holds on
every class, for any of the actual additive point identifications already
constructed. The torsion comparison then follows from the original
Kummer coefficient inclusion, without choosing another Picard dictionary.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open AlgebraicCurve NeronModelInfra GoodReductionJacobian EtaleCohomology
open AlgebraicCurves.Geometry.Schemes.Proofs
open Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso.AlgebraicGeometry.BCKerGlue

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F)

local instance : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase

local notation "C₀" => pullback M.toBase (𝟙 (Spec (CommRingCat.of K)))
local notation "q" => inv (pullback.fst M.toBase (𝟙 (Spec (CommRingCat.of K))))

private theorem nativePicard_section
    (x : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase) :
    M.multiplicativeGroupH1PicardEquiv
        (effectiveCartierMultiplicativeGroupH1
          (sectionEffectiveCartierDivisor M.toBase x.1 x.2)) =
      QuotientAddGroup.mk (Finsupp.single (M.pointEquivPlace x) (1 : ℤ)) := by
  change M.multiplicativeGroupH1PicardEquiv
    (Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact M.C) 0 1 rfl
      (effectiveCartierGenericUnitH0
        ⟨x.1.ker, (Scheme.Hom.isInvertible_ker_of_comp_eq_id x.1 x.2).isEffectiveCartier⟩)) = _
  rw [M.multiplicativeGroupH1PicardEquiv_connecting,
    M.genericUnitDivisorH0Equiv_cartier x.1.ker
      (Scheme.Hom.isInvertible_ker_of_comp_eq_id x.1 x.2), M.cartierModulus_point x]
  exact congrArg (fun E : Divisor K F => (QuotientAddGroup.mk E : Pic K F))
    (by simp only [Modulus.toDivisor, Finsupp.mapRange_single, Nat.cast_one])

private theorem graphPoint_nativePicard_pullback
    (x : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase) :
    let _ : IsIntegral C₀ := isIntegral_pullback_of_smooth_of_isAlgClosed M.toBase (𝟙 _)
    M.multiplicativeGroupH1PicardEquiv
        (etaleMultiplicativeGroupCohomologyPullback q 1
          (effectiveCartierMultiplicativeGroupH1
            (graphEffectiveCartierDivisor M.toBase (𝟙 _) x.1 x.2))) =
      QuotientAddGroup.mk (Finsupp.single (M.pointEquivPlace x) (1 : ℤ)) := by
  intro hC₀
  let D := graphEffectiveCartierDivisor M.toBase (𝟙 _) x.1 x.2
  have hI : D.1.comap q = x.1.ker := by
    apply ker_comap_eq_ker
    apply (cancel_mono (pullback.fst M.toBase (𝟙 (Spec (.of K))))).mp
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, graphOver_fst]
  have hD : (D.1.comap q).IsEffectiveCartier := by
    rw [hI]
    exact (sectionEffectiveCartierDivisor M.toBase x.1 x.2).2
  have he : (⟨D.1.comap q, hD⟩ : Scheme.EffectiveCartierDivisor M.C) =
      sectionEffectiveCartierDivisor M.toBase x.1 x.2 := Subtype.ext hI
  rw [effectiveCartierMultiplicativeGroupH1_pullback q D hD, he]
  exact M.nativePicard_section x

variable
  (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
  (D : GoodReductionJacobian.RelativePic0Designation K M.toBase)
  (hD : RelPicard.RepresentsRelSubPic M.toBase ε
    (RelPicard.algEquivZeroCut M.toBase ε) D)
  (aj : SchemeHomOver M.toBase D.toBase)


/-- The native Picard class of an actual Poincaré fibre is the same
Pic⁰ class under any actual additive point identification retaining the
Abel--Jacobi formula. Point-difference generation proves the assertion
on all classes, not only on the points in that formula. -/
theorem poincare_nativePicard_of_abelJacobi
    (hclass : ∀ x : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase,
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M.toBase ε.1 ε.2).idealModule))
    (e : Pic0 K F ≃+
      (hD.relativeGroupLaw (P := RelPicard.algEquivZeroGroupCut M.toBase ε)).AlgPoints
      (hD.relativeGroupLaw_isCommutative (P := RelPicard.algEquivZeroGroupCut M.toBase ε)) K)
    (hpoint : ∀ x : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase,
      ∃ Dv : Divisor.degZero (K := K) (F := F),
        (Dv : Divisor K F) = Finsupp.single (M.pointEquivPlace x) 1 -
          Finsupp.single (M.pointEquivPlace ε) 1 ∧
        (RelativeGroupLaw.AlgPoints.toPoint (e (Pic0.mk Dv))).1 = x.1 ≫ aj.1)
    (a : Pic0 K F) (τ : SchemeHomOver (𝟙 (Spec (.of K))) D.toBase)
    (hτ : (RelativeGroupLaw.AlgPoints.toPoint (e a)).1 = τ.1) :
    let _ : IsIntegral C₀ := isIntegral_pullback_of_smooth_of_isAlgClosed M.toBase (𝟙 _)
    M.multiplicativeGroupH1PicardEquiv
        (etaleMultiplicativeGroupCohomologyPullback q 1
          (invertibleModuleMultiplicativeGroupH1 (hD.poincare.pullbackAlong τ).isInvertible)) =
      H1Gm.ofPic0 K F a := by
  intro hC₀
  have : IsCurveOver K F := isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
    M.toBase M.ffEquiv M.ffEquiv_algebraMap
  let φ : (hD.relativeGroupLaw (P := RelPicard.algEquivZeroGroupCut M.toBase ε)).AlgPoints
      (hD.relativeGroupLaw_isCommutative (P := RelPicard.algEquivZeroGroupCut M.toBase ε)) K →+
      Pic K F :=
    M.multiplicativeGroupH1PicardEquiv.toAddMonoidHom.comp
      ((etaleMultiplicativeGroupCohomologyPullback q 1).comp
        (hD.poincareNativeH1Hom (P := RelPicard.algEquivZeroGroupCut M.toBase ε)))
  let f₁ := φ.comp e.toAddMonoidHom
  let f₂ := H1Gm.ofPic0 K F
  have heq : f₁ a = f₂ a := by
    apply AddMonoidHom.eqOn_closure (s :=
      {z : Pic0 K F | ∃ (v : Place K F)
        (hv : Finsupp.single v (1 : ℤ) - Finsupp.single (M.pointEquivPlace ε) 1 ∈
          Divisor.degZero (K := K) (F := F)),
        z = Pic0.mk ⟨Finsupp.single v 1 - Finsupp.single (M.pointEquivPlace ε) 1, hv⟩}) ?_
      (Pic0.mem_closure_mk_single_sub_single IsCurveOver.deg_eq_one_of_isAlgClosed
        (M.pointEquivPlace ε) a)
    rintro _ ⟨v, hv, rfl⟩
    let x := M.pointEquivPlace.symm v
    have hx : M.pointEquivPlace x = v := M.pointEquivPlace.apply_symm_apply v
    obtain ⟨Dv, hDv, hpt⟩ := hpoint x
    have hDv' : Dv =
        ⟨Finsupp.single v 1 - Finsupp.single (M.pointEquivPlace ε) 1, hv⟩ := by
      apply Subtype.ext
      rw [hDv, hx]
    rw [← hDv']
    let t : SchemeHomOver (𝟙 (Spec (.of K))) D.toBase :=
      ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
        ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩
    let Dx := graphEffectiveCartierDivisor M.toBase (𝟙 _) x.1 x.2
    let Dε := graphEffectiveCartierDivisor M.toBase (𝟙 _) ε.1 ε.2
    obtain ⟨i⟩ := hclass x
    have hi : invertibleModuleMultiplicativeGroupH1 (hD.poincare.pullbackAlong t).isInvertible =
        effectiveCartierMultiplicativeGroupH1 Dx - effectiveCartierMultiplicativeGroupH1 Dε :=
      invertibleModuleMultiplicativeGroupH1_eq_signedCartier
        (hD.poincare.pullbackAlong t).isInvertible Dx Dε i
    change M.multiplicativeGroupH1PicardEquiv
      (etaleMultiplicativeGroupCohomologyPullback q 1
        (hD.poincareNativeH1Hom (P := RelPicard.algEquivZeroGroupCut M.toBase ε)
          (e (Pic0.mk Dv)))) = H1Gm.ofPic0 K F (Pic0.mk Dv)
    rw [hD.poincareNativeH1Hom_apply_of_pointEq
      (P := RelPicard.algEquivZeroGroupCut M.toBase ε) (e (Pic0.mk Dv)) t hpt,
      hi, map_sub, map_sub, M.graphPoint_nativePicard_pullback x,
      M.graphPoint_nativePicard_pullback ε, H1Gm.ofPic0_mk, hDv]
    exact (QuotientAddGroup.mk_sub _ _ _).symm
  change M.multiplicativeGroupH1PicardEquiv
    (etaleMultiplicativeGroupCohomologyPullback q 1
      (hD.poincareNativeH1Hom (P := RelPicard.algEquivZeroGroupCut M.toBase ε) (e a))) = _ at heq
  rw [hD.poincareNativeH1Hom_apply_of_pointEq
    (P := RelPicard.algEquivZeroGroupCut M.toBase ε) (e a) τ hτ] at heq
  exact heq

variable
    (hclass : ∀ x : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase,
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M.toBase ε.1 ε.2).idealModule))
    (e : Pic0 K F ≃+
      (hD.relativeGroupLaw (P := RelPicard.algEquivZeroGroupCut M.toBase ε)).AlgPoints
      (hD.relativeGroupLaw_isCommutative (P := RelPicard.algEquivZeroGroupCut M.toBase ε)) K)
    (hpoint : ∀ x : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase,
      ∃ Dv : Divisor.degZero (K := K) (F := F),
        (Dv : Divisor K F) = Finsupp.single (M.pointEquivPlace x) 1 -
          Finsupp.single (M.pointEquivPlace ε) 1 ∧
        (RelativeGroupLaw.AlgPoints.toPoint (e (Pic0.mk Dv))).1 = x.1 ≫ aj.1)

include hclass hpoint in
/-- The original Kummer class of a Poincaré fibre has the same native
Picard torsion coordinate after the canonical identity base change. -/
theorem poincare_nativeKummer_of_abelJacobi
    {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K))
    (a : Pic0.torsion K F n)
    (τ : SchemeHomOver (𝟙 (Spec (.of K))) D.toBase)
    (hτ : (RelativeGroupLaw.AlgPoints.toPoint (e a.val)).1 = τ.1)
    (κ : Sheaf.H.{u} (etaleRootsOfUnitySheaf C₀ n) 1) :
    let _ : IsIntegral C₀ := isIntegral_pullback_of_smooth_of_isAlgClosed M.toBase (𝟙 _)
    etaleRootsOfUnityH1ToMultiplicativeGroup C₀ n κ =
        invertibleModuleMultiplicativeGroupH1 (hD.poincare.pullbackAlong τ).isInvertible →
      M.nativeKummerH1PicardTorsionEquiv hn hnK
        (etaleRootsOfUnityCohomologyPullback q n 1 κ) = a := by
  intro hC₀ hκ
  apply Subtype.ext
  apply H1Gm.ofPic0_injective K F
  rw [M.nativeKummerH1PicardTorsionEquiv_ofPic0,
    etaleRootsOfUnityH1ToMultiplicativeGroup_pullback, hκ]
  exact M.poincare_nativePicard_of_abelJacobi ε D hD aj hclass e hpoint a.val τ hτ

include hclass hpoint in
/-- The finite constant coefficient coordinate of that same Poincaré
class is computed by the original coherent-root Kummer equivalence. -/
theorem poincare_nativeFiniteLevel_of_abelJacobi
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
    (a : Pic0.torsion K F (ℓ ^ (n + 1)))
    (τ : SchemeHomOver (𝟙 (Spec (.of K))) D.toBase)
    (hτ : (RelativeGroupLaw.AlgPoints.toPoint (e a.val)).1 = τ.1)
    (κ : Sheaf.H.{u} (etaleRootsOfUnitySheaf C₀ (ℓ ^ (n + 1))) 1) :
    let _ : IsIntegral C₀ := isIntegral_pullback_of_smooth_of_isAlgClosed M.toBase (𝟙 _)
    etaleRootsOfUnityH1ToMultiplicativeGroup C₀ (ℓ ^ (n + 1)) κ =
        invertibleModuleMultiplicativeGroupH1 (hD.poincare.pullbackAlong τ).isInvertible →
      M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n
        ((finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 1).symm
          (etaleRootsOfUnityCohomologyPullback q (ℓ ^ (n + 1)) 1 κ)) = a := by
  intro hC₀ hκ
  change M.nativeKummerH1PicardTorsionEquiv
    (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
    (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1))
    (finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 1
      ((finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 1).symm
        (etaleRootsOfUnityCohomologyPullback q (ℓ ^ (n + 1)) 1 κ))) = a
  rw [AddEquiv.apply_symm_apply]
  exact M.poincare_nativeKummer_of_abelJacobi ε D hD aj hclass e hpoint
    (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
    (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)) a τ hτ κ hκ

end AlgebraicCurve.CurveModel
