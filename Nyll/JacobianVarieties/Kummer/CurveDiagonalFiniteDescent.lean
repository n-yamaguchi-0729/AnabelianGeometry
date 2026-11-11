/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
public import Nyll.AlgebraicCurves.Models.Kummer.CurveNativeH1Picard
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProductIntegral
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.EtaleCohomology.Classical.AbelianCechComponentDetection
public import Nyll.EtaleCohomology.Classical.AbelianCechPullback
public import Nyll.EtaleCohomology.Classical.AbelianCechResidualDescent
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicCupH1Anticommutativity
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.CartierAdicCycleClass
public import Nyll.EtaleCohomology.Classical.CartierCycleClass
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.CupCechKernelProduct
public import Nyll.EtaleCohomology.Classical.CurveOverlapComponents
public import Nyll.EtaleCohomology.Classical.DiagonalDivisorBundle
public import Nyll.EtaleCohomology.Classical.DiagonalPoincareFamily
public import Nyll.EtaleCohomology.Classical.ExternalCupPullbackComposition
public import Nyll.EtaleCohomology.Classical.FiniteCechKernelCup
public import Nyll.EtaleCohomology.Classical.FiniteCechKernelCupRestriction
public import Nyll.EtaleCohomology.Classical.FiniteDiagonalSections
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.FiniteLevelScalarApproximation
public import Nyll.EtaleCohomology.Classical.GraphCartierCycleClass
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.RationalKunnethSections
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.GaloisSections
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
public import Nyll.JacobianVarieties.Kummer.CurveDiagonalFirstRelation
public import Nyll.JacobianVarieties.Kummer.CurveDiagonalFiniteKernel
public import Nyll.JacobianVarieties.Kummer.CurveDiagonalFiniteTransgression
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionBaseChangeDescent
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionCupOverlap
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionCupSum
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionIntegralRoot
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionRoot
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionRootNativeOverlap
public import Nyll.JacobianVarieties.Kummer.CurveNativeCupPairing
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleConnected
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Module.LinearMap.End

/-!
# Descent of the finite normalized diagonal from an actual division root

The retained Picard division root and the original finite cup kernels
have the same overlap classes after multiplication by the denominator
of the integral tensor. Their difference descends from the parameter
curve. The original point section kills that difference. Every class,
coefficient map and covering kernel in this calculation is the original
one used by the finite and adic cohomology constructions.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Abelian
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicCurve.CurveModel

/-- The actual point section kills a finite sum of positive-degree external cups. -/
private theorem finiteExternalCupSum_kunnethSectionRight_eq_zero
    {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    {ι : Type*} (S : Finset ι)
    (x : ι → finiteLevelCohomology X ℓ n 1) (y : ι → finiteLevelCohomology Y ℓ n 1) :
    finiteLevelCohomologyPullback ℓ (kunnethSectionRight f g p hp) n 2
      (∑ v ∈ S, finiteLevelCup (pullback f g) ℓ n 1 1 2 rfl
        (finiteLevelCohomologyPullback ℓ (pullback.fst f g) n 1 (x v))
        (finiteLevelCohomologyPullback ℓ (pullback.snd f g) n 1 (y v))) = 0 := by
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro v _
  exact finiteLevelCup_kunnethSectionRight_eq_zero f g p hp ℓ n 0 1 2 rfl (x v) (y v)

private theorem finiteDiagonalSignedCycleClass_eq_integralCupSum_of_root_descent
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    [GeometricallyIntegral c] (p : Spec (.of K) ⟶ C) (hp : p ≫ c = 𝟙 _)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
    (D : RelativePic0Designation K c)
    (hD : RepresentsRelSubPic c ⟨p, hp⟩ (algEquivZeroCut c ⟨p, hp⟩) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (B : FiniteEtale C) [IsIntegral B.left] [Surjective B.hom] :
    let aj : SchemeHomOver c D.toBase := diagonalPicardClassifyingMap c p hp D hD
    ∀ (i : B.left ⟶ hD.divisionPullback (P := algEquivZeroGroupCut c ⟨p, hp⟩) aj (ℓ ^ (n + 1)))
      (hi : i ≫ hD.divisionProjection (P := algEquivZeroGroupCut c ⟨p, hp⟩) aj (ℓ ^ (n + 1)) =
        B.hom),
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    let M := literalCurveModel c
    let Y := pullback c c
    let _ : IsIntegral Y := isIntegral_pullback_of_smooth_of_isAlgClosed c c
    let p₂ := pullback.snd c c
    let cY := p₂ ≫ c
    let z : SchemeHomOver (B.hom ≫ c)
        (hD.divisionStructure (P := algEquivZeroGroupCut c ⟨p, hp⟩) aj (ℓ ^ (n + 1))) :=
      ⟨i, (Category.assoc i
        (hD.divisionProjection (P := algEquivZeroGroupCut c ⟨p, hp⟩) aj (ℓ ^ (n + 1))) c).symm.trans
        (congrArg (fun f => f ≫ c) hi)⟩
    let hL :=
      ((hD.divisionRootFamily (P := algEquivZeroGroupCut c ⟨p, hp⟩)
        aj (ℓ ^ (n + 1))).isInvertible).pullback (baseChangeSnd c z)
    let T : C.Etale := Scheme.Etale.mk (𝟙 C)
    let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) C
    let q := finiteEtaleCoverBaseMap C B
    let hq := finiteEtaleCoverBaseMap_covering C B
    let BC := etaleBaseChange p₂
    let V := BC.obj ((finiteEtaleInclusion C).obj B)
    let eB := diagonalParameterProductCoverBaseChangeIso c B
    let cB : B.left ⟶ Spec (.of K) := B.hom ≫ c
    let hU : IsIntegral (diagonalParameterProductCover c B).left :=
      isIntegral_pullback_of_smooth_of_isAlgClosed c cB
    let _ : IsIntegral
        ((finiteEtaleInclusion Y).obj (diagonalParameterProductCover c B)).left := hU
    let _ : IsIntegral V.left := by
      have : IsIso eB.hom.left :=
        inferInstanceAs
          (IsIso ((Scheme.Etale.forget Y ⋙ CategoryTheory.Over.forget Y).map eB.hom))
      exact IsIntegral.of_isIso eB.hom.left
    let hTB := hT.isTerminalObj BC T
    let qB := BC.map q
    let hqB := etaleBaseChange_singleton_covering p₂ q hq
    let A := abelianCechAugmentationSequence Y.smallEtaleTopology hTB qB
    let hA := abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hTB qB hqB
    let F := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
      (ellPowerCoefficients.{u} ℓ n)
    ∀ (r : ℤ_[ℓ]) (S : Finset (ellAdicCohomology C ℓ 1 × ellAdicCohomology C ℓ 1)),
      M.IsNativeIntegralCupExpansion ℓ hℓ r S →
      ∀ (aμ : Ext.{u} A.X₁ (etaleRootsOfUnitySheaf Y (ℓ ^ (n + 1))) 1),
        (aμ.comp (Ext.mk₀ (kernel.ι (etaleMultiplicativeGroupPower Y (ℓ ^ (n + 1))))) (add_zero 1) =
          (Ext.mk₀ A.f).comp
            (invertibleModuleCohomologyPresheafH1 V (hL.pullback eB.inv.left))
            (zero_add 1)) →
        let aFinite : Ext.{u} A.X₁ F 1 :=
          aμ.comp (Ext.mk₀ (ellPowerConstantKummerKernelIso cY ℓ hℓ n).inv) (add_zero 1)
        hA.extClass.comp aFinite (show 1 + 1 = 2 from rfl) =
          -(finiteEffectiveCartierCycleClass (pullback.snd c c ≫ c) ℓ hℓ n
              (graphEffectiveCartierDivisor c c (𝟙 C) (Category.id_comp c)) -
            finiteEffectiveCartierCycleClass (pullback.snd c c ≫ c) ℓ hℓ n
              (diagonalEdgeEffectiveCartierDivisor c p hp)) →
        r • (finiteEffectiveCartierCycleClass (pullback.snd c c ≫ c) ℓ hℓ n
            (graphEffectiveCartierDivisor c c (𝟙 C) (Category.id_comp c)) -
          finiteEffectiveCartierCycleClass (pullback.snd c c ≫ c) ℓ hℓ n
            (diagonalEdgeEffectiveCartierDivisor c p hp)) =
          ∑ v ∈ S, finiteLevelCup (pullback c c) ℓ n 1 1 2 rfl
            (finiteLevelCohomologyPullback ℓ (pullback.fst c c) n 1
              (ellAdicProjection C ℓ 1 n v.1))
            (finiteLevelCohomologyPullback ℓ (pullback.snd c c) n 1
              (ellAdicProjection C ℓ 1 n v.2)) := by
  intro aj i hi algKC M Y hY p₂ cY z hL T hT q hq BC V eB cB hU hUI hVI
    hTB qB hqB A hA F r S hS aμ hcoeff aFinite ha
  classical
  let p₁ := pullback.fst c c
  have : GeometricallyConnected c := GeometricallyIrreducible.geometricallyConnected c
  let α := finiteEffectiveCartierCycleClass cY ℓ hℓ n
      (graphEffectiveCartierDivisor c c (𝟙 C) (Category.id_comp c)) -
    finiteEffectiveCartierCycleClass cY ℓ hℓ n (diagonalEdgeEffectiveCartierDivisor c p hp)
  let externalSum := ∑ v ∈ S, finiteLevelCup Y ℓ n 1 1 2 rfl
    (finiteLevelCohomologyPullback ℓ p₁ n 1 (ellAdicProjection C ℓ 1 n v.1))
    (finiteLevelCohomologyPullback ℓ p₂ n 1 (ellAdicProjection C ℓ 1 n v.2))
  change r • α = externalSum
  obtain ⟨d, hd, hedge⟩ :=
    exists_finiteDiagonalIntegralCupKernel_firstRelation c p hp ℓ hℓ n D hD B i hi
      r S hS aμ hcoeff
  let cupSum : Ext.{u} A.X₁ F 1 := ∑ v ∈ S,
    finiteCechKernelCupClass Y ℓ n hTB qB
      (finiteCechKernelPullback p₂ ℓ n hT q hq (d (ellAdicProjection C ℓ 1 n v.2)))
      (finiteLevelCohomologyPullback ℓ p₁ n 1 (ellAdicProjection C ℓ 1 n v.1))
  have hcup := finiteExternalCupKernelSum_transgression p₂ ℓ n hT q hq S
    (fun v => finiteLevelCohomologyPullback ℓ p₁ n 1 (ellAdicProjection C ℓ 1 n v.1))
    (fun v => ellAdicProjection C ℓ 1 n v.2) d hd
  let σ := kunnethSectionRight c c p hp
  have hα : finiteLevelCohomologyPullback ℓ σ n 2 α = 0 :=
    finiteDiagonalSignedCycleClass_kunnethSectionRight c p hp ℓ hℓ n
  have hexternal : finiteLevelCohomologyPullback ℓ σ n 2 externalSum = 0 :=
    finiteExternalCupSum_kunnethSectionRight_eq_zero c c p hp ℓ n S
      (fun v => ellAdicProjection C ℓ 1 n v.1) (fun v => ellAdicProjection C ℓ 1 n v.2)
  exact finiteTensor_eq_of_first_relation p₂ σ (kunnethSectionRight_snd c c p hp)
    ℓ n hT q hq aFinite cupSum α externalSum r ha hcup hedge hα hexternal

/-- An actual Picard division root identifies the finite signed diagonal with its cup sum. -/
theorem finiteDiagonalSignedCycleClass_eq_integralCupSum_of_division_root
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    [GeometricallyIntegral c]
    (p : Spec (.of K) ⟶ C) (hp : p ≫ c = 𝟙 _)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))
    (D : RelativePic0Designation K c)
    (hD : RepresentsRelSubPic c ⟨p, hp⟩ (algEquivZeroGroupCut c ⟨p, hp⟩).toSubPicCondition D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (B : FiniteEtale C) [IsIntegral B.left] [Surjective B.hom] (n : ℕ) :
    let N := ℓ ^ (n + 1)
    let aj := diagonalPicardClassifyingMap c p hp D hD
    ∀ (i : B.left ⟶ hD.divisionPullback aj N)
      (hi : i ≫ hD.divisionProjection aj N = B.hom),
      let z : SchemeHomOver (B.hom ≫ c) (hD.divisionStructure aj N) :=
        ⟨i, (Category.assoc i (hD.divisionProjection aj N) c).symm.trans
          (congrArg (fun q => q ≫ c) hi)⟩
      ((Scheme.Modules.pullback
          (baseChangeSnd c (⟨B.hom, rfl⟩ : SchemeHomOver (B.hom ≫ c) c))).obj
          ((graphEffectiveCartierDivisor c c (𝟙 C) (Category.id_comp c)).1.invModule ⊗
            (diagonalEdgeEffectiveCartierDivisor c p hp).1.module) ≅
        ((Scheme.Modules.pullback (baseChangeSnd c z)).obj
          (hD.divisionRootFamily aj N).L).tensorPow N) →
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    let M := literalCurveModel c
    let _ : IsIntegral (pullback c c) := isIntegral_pullback_of_smooth_of_isAlgClosed c c
    ∀ (r : ℤ_[ℓ]) (S : Finset (ellAdicCohomology C ℓ 1 × ellAdicCohomology C ℓ 1)),
      (∀ z : ellAdicCohomology C ℓ 1, ∑ v ∈ S,
        M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl z v.2 • v.1 = (-r) • z) →
        r • (finiteEffectiveCartierCycleClass (pullback.snd c c ≫ c) ℓ hℓ n
            (graphEffectiveCartierDivisor c c (𝟙 C) (Category.id_comp c)) -
          finiteEffectiveCartierCycleClass (pullback.snd c c ≫ c) ℓ hℓ n
            (diagonalEdgeEffectiveCartierDivisor c p hp)) =
          ∑ v ∈ S, finiteLevelCup (pullback c c) ℓ n 1 1 2 rfl
            (finiteLevelCohomologyPullback ℓ (pullback.fst c c) n 1
              (ellAdicProjection C ℓ 1 n v.1))
            (finiteLevelCohomologyPullback ℓ (pullback.snd c c) n 1
              (ellAdicProjection C ℓ 1 n v.2)) := by
  intro N aj i hi z eRoot algKC M hY r S hS
  classical
  have hSNative : M.IsNativeIntegralCupExpansion ℓ hℓ r S := hS
  have : GeometricallyConnected c := GeometricallyIrreducible.geometricallyConnected c
  let Y := pullback c c
  let p₁ := pullback.fst c c
  let p₂ := pullback.snd c c
  let cY := p₂ ≫ c
  have hn : 0 < N := pow_pos (Fact.out : ℓ.Prime).pos (n + 1)
  have hnK : IsUnit (N : K) := by
    simpa only [N, Nat.cast_pow] using hℓ.pow (n + 1)
  let DD := graphEffectiveCartierDivisor c c (𝟙 C) (Category.id_comp c)
  let EE := diagonalEdgeEffectiveCartierDivisor c p hp
  let α := finiteEffectiveCartierCycleClass cY ℓ hℓ n DD -
    finiteEffectiveCartierCycleClass cY ℓ hℓ n EE
  let externalSum := ∑ v ∈ S, finiteLevelCup Y ℓ n 1 1 2 rfl
    (finiteLevelCohomologyPullback ℓ p₁ n 1 (ellAdicProjection C ℓ 1 n v.1))
    (finiteLevelCohomologyPullback ℓ p₂ n 1 (ellAdicProjection C ℓ 1 n v.2))
  change r • α = externalSum
  have : PreGaloisCategory.IsConnected B := FiniteEtale.isConnected_of_connectedSpace_left B
  let hL := (hD.divisionRootFamily aj N).isInvertible.pullback (baseChangeSnd c z)
  let T : C.Etale := Scheme.Etale.mk (𝟙 C)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) C
  let q := finiteEtaleCoverBaseMap C B
  let hq := finiteEtaleCoverBaseMap_covering C B
  let BC := etaleBaseChange p₂
  let hTB := hT.isTerminalObj BC T
  let qB := BC.map q
  let hqB := etaleBaseChange_singleton_covering p₂ q hq
  let A := abelianCechAugmentationSequence Y.smallEtaleTopology hTB qB
  let hA := abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hTB qB hqB
  let F := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (ellPowerCoefficients ℓ n)
  obtain ⟨aμ, hcoeff, haμ⟩ := diagonalParameterProductBaseChange_root_descent
    c B N DD EE hL eRoot hn (etaleKummerExponentUnit_of_base cY hnK)
  let aFinite : Ext.{u} A.X₁ F 1 :=
    aμ.comp (Ext.mk₀ (ellPowerConstantKummerKernelIso cY ℓ hℓ n).inv) (add_zero 1)
  let tr : Ext.{u} A.X₁ F 1 →+ finiteLevelCohomology Y ℓ n 2 :=
    hA.extClass.precomp F (show 1 + 1 = 2 from rfl)
  have ha : tr aFinite = -α :=
    signedRootFinite_transgression cY ℓ hℓ n hTB qB hqB DD EE aμ haμ
  exact finiteDiagonalSignedCycleClass_eq_integralCupSum_of_root_descent
    c p hp ℓ hℓ n D hD B i hi r S hSNative aμ hcoeff ha

end AlgebraicCurve.CurveModel
