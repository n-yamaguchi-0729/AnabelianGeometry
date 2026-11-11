/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.ProperTorsionPoints
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProductIntegral
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Projective.InvertibleTensorPow
public import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.IsPullbackBaseChangeSnd
public import Nyll.AlgebraicCurves.Geometry.Picard.DivisionPullback
public import Nyll.AlgebraicCurves.Geometry.Picard.DivisionPullbackCocycle
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Geometry.Picard.Poincare.PicardRepresentabilityPoincarePullbackOneIso
public import Nyll.EtaleCohomology.Classical.InvertibleCycleClass
public import Nyll.EtaleCohomology.Classical.InvertibleCycleTensor
public import Nyll.EtaleCohomology.Classical.InvertibleDominantPullback
public import Nyll.EtaleCohomology.Classical.KummerH1Functoriality
public import Nyll.EtaleCohomology.Classical.KummerH1Kernel
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.ProperKummerH1
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionKummerTransition
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionTransition
public import Nyll.JacobianVarieties.Picard.Poincare.PicardRepresentabilityPoincarePullbackPowIsoTensorPow
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Constant native Kummer classes on the actual division overlap

On an integral proper parameter overlap, the original torsion
difference comes from one actual rational Picard torsion point.
Its original Poincaré line bundle gives a native Kummer class on
the original curve over the identity base. Pulling back that class
is the original transition class, by the actual line-bundle
comparison and the original Kummer coefficient inclusion.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open NeronModelInfra GoodReductionJacobian EtaleCohomology

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}}
  [IsIntegral C] {c : C ⟶ Spec (.of K)} [Smooth c] [IsProper c]
  {ε : SchemeHomOver (𝟙 (Spec (.of K))) c}
  {P : SubPicGroupCondition c ε} {D : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
  [Smooth D.toBase] [IsProper D.toBase]
  {T : Scheme.{u}} {t : T ⟶ Spec (.of K)}
  (a : SchemeHomOver t D.toBase) (n : ℕ)
  {W : Scheme.{u}} [IsIntegral W]
  (w : W ⟶ Spec (.of K)) [IsProper w]

/-- The actual transition is pulled back from a native Kummer class
of its actual rational Picard torsion point. The original difference,
line-bundle isomorphism and coefficient inclusion are all retained. -/
theorem divisionTransitionKummerClass_exists_constant
    (hn : 0 < n) (hnK : IsUnit (n : K))
    (x y : SchemeHomOver w (h.divisionStructure a n))
    (hxy : postComp (h.divisionBaseMap a n) x =
      postComp (h.divisionBaseMap a n) y) :
    let C₀ := pullback c (𝟙 (Spec (.of K)))
    let _ : IsIntegral C₀ := isIntegral_pullback_of_smooth_of_isAlgClosed c (𝟙 _)
    let Y := pullback c w
    let _ : IsIntegral Y := isIntegral_pullback_of_smooth_of_isAlgClosed c w
    let v : SchemeHomOver w (𝟙 (Spec (.of K))) := ⟨w, Category.comp_id w⟩
    let q := baseChangeSnd c v
    ∃ τ : SchemeHomOver (𝟙 (Spec (.of K))) D.toBase,
      h.relativeGroupLaw.IsTorsionPoint (𝟙 _) n τ ∧
        postComp τ v = h.divisionDifference a n x y ∧
        Nonempty ((Scheme.Modules.pullback q).obj (h.poincare.pullbackAlong τ).L ≅
          (h.divisionTransitionFamily a n x y).L) ∧
        ∃ κ : Sheaf.H.{u} (etaleRootsOfUnitySheaf C₀ n) 1,
          etaleRootsOfUnityH1ToMultiplicativeGroup C₀ n κ =
            invertibleModuleMultiplicativeGroupH1 (h.poincare.pullbackAlong τ).isInvertible ∧
          etaleRootsOfUnityCohomologyPullback q n 1 κ =
            h.divisionTransitionKummerClass a n hn hnK x y hxy := by
  intro C₀ hC₀ Y hY v q
  obtain ⟨τ, hτ, hconstant⟩ := h.relativeGroupLaw.isTorsionPoint_exists_constant
    h.relativeGroupLaw_isCommutative w n hnK (h.divisionDifference a n x y)
    (h.divisionDifference_isTorsion a n x y hxy)
  change postComp τ v = h.divisionDifference a n x y at hconstant
  let e : (Scheme.Modules.pullback q).obj (h.poincare.pullbackAlong τ).L ≅
      (h.divisionTransitionFamily a n x y).L :=
    (Scheme.Modules.pullbackComp q (baseChangeSnd c τ)).app h.poincare.L ≪≫
      (Scheme.Modules.pullbackCongr
        ((baseChangeSnd_comp c τ v).trans
          (congrArg (baseChangeSnd c) hconstant))).app h.poincare.L
  let G := h.relativeGroupLaw
  let : Group (SchemeHomOver (𝟙 (Spec (.of K))) D.toBase) := G.pointGroup (𝟙 _)
  have hpow : τ ^ n = 1 := by
    exact (G.pointGroup_pow_eq_nsmul (𝟙 _) τ n).trans hτ
  obtain ⟨ePow⟩ := h.nonempty_poincare_pullbackAlong_pow_iso_tensorPow (𝟙 _) τ n
  rw [hpow] at ePow
  have hone : Nonempty ((h.poincare.pullbackAlong
      (1 : SchemeHomOver (𝟙 (Spec (.of K))) D.toBase)).L ≅ 𝟙_ _) := by
    let := h.grpObj
    exact h.nonempty_poincare_pullbackAlong_one_iso (Over.mk (𝟙 _))
  obtain ⟨eOne⟩ := hone
  let hL := (h.poincare.pullbackAlong τ).isInvertible
  have hkill : n • invertibleModuleMultiplicativeGroupH1 hL = 0 := by
    have he := invertibleModuleMultiplicativeGroupH1_iso (hL.tensorPow n)
      (Scheme.Modules.isInvertible_unit C₀) (ePow.symm ≪≫ eOne)
    rw [invertibleModuleMultiplicativeGroupH1_tensorPow,
      invertibleModuleMultiplicativeGroupH1_unit] at he
    exact he
  let d₀ := pullback.snd c (𝟙 (Spec (.of K)))
  let κ := (properIntegralKummerH1EquivPowerKernel d₀ hn hnK).symm
    ⟨invertibleModuleMultiplicativeGroupH1 hL, hkill⟩
  have hκ : etaleRootsOfUnityH1ToMultiplicativeGroup C₀ n κ =
      invertibleModuleMultiplicativeGroupH1 hL :=
    congrArg Subtype.val ((properIntegralKummerH1EquivPowerKernel d₀ hn hnK).apply_symm_apply _)
  refine ⟨τ, hτ, hconstant, ⟨e⟩, κ, hκ, ?_⟩
  have : Surjective w := ⟨Function.surjective_to_subsingleton _⟩
  have : Surjective q := MorphismProperty.of_isPullback
    (P := @Surjective) (isPullback_baseChangeSnd c v).flip
      (inferInstance : Surjective w)
  apply (properIntegralKummerH1EquivPowerKernel (pullback.snd c w ≫ w) hn hnK).injective
  apply Subtype.ext
  change etaleRootsOfUnityH1ToMultiplicativeGroup Y n
    (etaleRootsOfUnityCohomologyPullback q n 1 κ) =
      etaleRootsOfUnityH1ToMultiplicativeGroup Y n
        (h.divisionTransitionKummerClass a n hn hnK x y hxy)
  rw [etaleRootsOfUnityH1ToMultiplicativeGroup_pullback, hκ,
    invertibleModuleMultiplicativeGroupH1_dominantPullback q q.surjective.denseRange,
    h.divisionTransitionKummerClass_inclusion]
  exact invertibleModuleMultiplicativeGroupH1_iso (hL.pullback q)
    (h.divisionTransitionFamily a n x y).isInvertible e

end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
