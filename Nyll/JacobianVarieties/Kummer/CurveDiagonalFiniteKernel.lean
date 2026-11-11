/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProductIntegral
public import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionDescent

public import Nyll.JacobianVarieties.Kummer.CurveDiagonalFirstRelation
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionCupOverlap
public import Nyll.EtaleCohomology.Classical.DiagonalPoincareFamily
public import Nyll.EtaleCohomology.Classical.FiniteCechKernelCup
public import Nyll.EtaleCohomology.Classical.AbelianCechPullback
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected

/-!
# Original finite cup kernels with their first relation

The Picard and torsion comparison data construct the original finite cup
kernels and prove their first relation here. Consumers retain only those
kernels and their proved equations, avoiding repeated elimination of the
large dependent comparison data.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Abelian
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicCurve.CurveModel

/-- Construct original covering-kernel representatives and their proved first
relation with the supplied actual root-descent class. The Picard and torsion
comparison data remain internal to this construction. -/
theorem exists_finiteDiagonalIntegralCupKernel_firstRelation
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
    let p₁ := pullback.fst c c
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
    let A := abelianCechAugmentationSequence Y.smallEtaleTopology hTB qB
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
        ∃ d : finiteLevelCohomology C ℓ n 1 →
            ((abelianCechAugmentationSequence C.smallEtaleTopology hT q).X₁ ⟶
              (constantSheaf C.smallEtaleTopology AddCommGrpCat.{u}).obj
                (ellPowerCoefficients.{u} ℓ n)),
          (∀ b : finiteLevelCohomology C ℓ n 1,
            (abelianCechAugmentationSequence_shortExact
              C.smallEtaleTopology hT q hq).extClass.comp (Ext.mk₀ (d b))
                (add_zero 1) = b) ∧
          (let cupSum : Ext.{u} A.X₁ F 1 := ∑ v ∈ S,
            finiteCechKernelCupClass Y ℓ n hTB qB
              (finiteCechKernelPullback p₂ ℓ n hT q hq
                (d (ellAdicProjection C ℓ 1 n v.2)))
              (finiteLevelCohomologyPullback ℓ p₁ n 1 (ellAdicProjection C ℓ 1 n v.1))
           let aScaled := r.appr (n + 1) • aFinite
           (Ext.mk₀ (abelianCechFirstRelationMap Y.smallEtaleTopology hTB qB)).comp
               aScaled (zero_add 1) =
             (Ext.mk₀ (abelianCechFirstRelationMap Y.smallEtaleTopology hTB qB)).comp
               cupSum (zero_add 1)) := by
  intro aj i hi algKC M Y p₁ p₂ cY z hL T hT q hq BC V eB cB hU hUI hVI
    hTB qB A F r S hS aμ hcoeff aFinite
  have : PreGaloisCategory.IsConnected B := FiniteEtale.isConnected_of_connectedSpace_left B
  obtain ⟨e, hpoint, τe, hτe, -, d, hd, hvalues⟩ :=
    JacobianVarieties.Kummer.exists_diagonalDivision_nativeCupKernels c ⟨p, hp⟩ D hD aj
      (fun L _ t x => diagonalPicardClassifyingMap_fieldPointIso c p hp D hD L t x)
      ℓ hℓ n B i hi
  refine ⟨d, hd, ?_⟩
  intro cupSum aScaled
  exact finiteDiagonalIntegralCup_firstRelation c p hp ℓ hℓ n D hD B i hi
    r S hS aμ hcoeff e hpoint τe hτe d hvalues

end AlgebraicCurve.CurveModel
