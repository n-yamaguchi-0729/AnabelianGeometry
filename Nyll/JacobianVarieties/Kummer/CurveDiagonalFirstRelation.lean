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
# First relations of the division root and integral cup representatives

The retained Picard division root and the original finite cup kernels
have the same overlap classes after multiplication by the denominator
of the integral tensor. This first-relation calculation compares their actual
overlap restrictions. Every class,
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

universe u₀ u₁ u₂ v₀ v₁ v₂

/-- Equal supplied overlap projections give equal mapped edge morphisms. -/
private theorem mapPullbackLift_postcomp_eq
    {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
    [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]
    (G : C₀ ⥤ C₁) (Q : C₁ ⥤ C₂)
    {T V W : C₀} (q : V ⟶ T) (hB : IsTerminal (G.obj T))
    [HasPullback (G.map q) (G.map q)]
    (x₀ x₁ y₀ y₁ : W ⟶ V) (hx : x₀ = y₀) (hy : x₁ = y₁)
    {D E : C₂} (e : Q.obj (pullback (G.map q) (G.map q)) ⟶ D) (r : D ⟶ E) :
    Q.map (pullback.lift (G.map x₀) (G.map x₁)
        (hB.hom_ext (G.map x₀ ≫ G.map q) (G.map x₁ ≫ G.map q))) ≫ e ≫ r =
      Q.map (pullback.lift (G.map y₀) (G.map y₁)
        (hB.hom_ext (G.map y₀ ≫ G.map q) (G.map y₁ ≫ G.map q))) ≫ e ≫ r := by
  cases hx
  cases hy
  rfl

/-- Compare a scaled class and a second class through an additive restriction. -/
private theorem scaled_restriction_eq
    {A H : Type*} [AddMonoid A] [AddMonoid H]
    (P : A →+ H) (k : ℕ) (a b : A) (x y : H)
    (ha : P a = x) (hb : P b = y) (hscale : k • x = y) :
    P (k • a) = P b :=
  (map_nsmul P k a).trans
    ((congrArg (fun z : H => k • z) ha).trans (hscale.trans hb.symm))

/-- The integral family contracts to minus the denominator times the identity
under the original native cup pairing. -/
def IsNativeIntegralCupExpansion
    {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))
    (r : ℤ_[ℓ]) (S : Finset (ellAdicCohomology M.C ℓ 1 × ellAdicCohomology M.C ℓ 1)) :
    Prop :=
  ∀ z : ellAdicCohomology M.C ℓ 1, ∑ v ∈ S,
    M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl z v.2 • v.1 = (-r) • z

/-- The original division-root and cup representatives have equal first relations. -/
theorem finiteDiagonalIntegralCup_firstRelation
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    [GeometricallyIntegral c] (p : Spec (.of K) ⟶ C) (hp : p ≫ c = 𝟙 _)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
    (D : RelativePic0Designation K c)
    (hD : RepresentsRelSubPic c ⟨p, hp⟩ (algEquivZeroCut c ⟨p, hp⟩) D)
    [Smooth D.toBase] [IsProper D.toBase]
    (B : FiniteEtale C) [IsIntegral B.left] [Surjective B.hom] :
    let aj : SchemeHomOver c D.toBase := diagonalPicardClassifyingMap c p hp D hD
    ∀ (i : B.left ⟶ hD.divisionPullback (P := algEquivZeroGroupCut c ⟨p, hp⟩) aj (ℓ ^ (n + 1)))
      (hi : i ≫ hD.divisionProjection (P := algEquivZeroGroupCut c ⟨p, hp⟩) aj (ℓ ^ (n + 1)) =
        B.hom),
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    let M := literalCurveModel c
    let _ : HasPrincipalDivisors K C.functionField :=
      (literalCurveModel_functionField_properties c).1.toHasPrincipalDivisors
    let Y := pullback c c
    let p₁ := pullback.fst c c
    let p₂ := pullback.snd c c
    let cY := p₂ ≫ c
    let z : SchemeHomOver (B.hom ≫ c)
        (hD.divisionStructure (P := algEquivZeroGroupCut c ⟨p, hp⟩) aj (ℓ ^ (n + 1))) :=
      ⟨i, (Category.assoc i
        (hD.divisionProjection (P := algEquivZeroGroupCut c ⟨p, hp⟩) aj (ℓ ^ (n + 1))) c).symm.trans
        (congrArg (fun f => f ≫ c) hi)⟩
    let _ : postComp (hD.divisionBaseMap (P := algEquivZeroGroupCut c ⟨p, hp⟩) aj (ℓ ^ (n + 1))) z =
        (⟨B.hom, rfl⟩ : SchemeHomOver (B.hom ≫ c) c) := Subtype.ext hi
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
        let G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ⟨p, hp⟩) hD
        let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
          (P := algEquivZeroGroupCut c ⟨p, hp⟩) hD
        let Np : ℕ+ := ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos (n + 1)⟩
        let hnK : IsUnit ((Np : ℕ) : K) := by
          change IsUnit ((ℓ ^ (n + 1) : ℕ) : K)
          simpa only [Nat.cast_pow] using hℓ.pow (n + 1)
        ∀ (e : Pic0 K C.functionField ≃+ G.AlgPoints hc K),
          (∀ x : SchemeHomOver (𝟙 (Spec (.of K))) c,
            ∃ Dv : Divisor.degZero (K := K) (F := C.functionField),
              (Dv : Divisor K C.functionField) = Finsupp.single (M.pointEquivPlace x) 1 -
                Finsupp.single (M.pointEquivPlace ⟨p, hp⟩) 1 ∧
              (RelativeGroupLaw.AlgPoints.toPoint (e (Pic0.mk Dv))).1 = x.1 ≫ aj.1) →
          ∀ (τe : Pic0.torsion K C.functionField (ℓ ^ (n + 1)) ≃+
            ProCGroups.torsionLevel (G.AlgPoints hc K) Np),
            (∀ x, (τe x).1 = e x.1) →
            ∀ (d : finiteLevelCohomology C ℓ n 1 →
                ((abelianCechAugmentationSequence C.smallEtaleTopology hT q).X₁ ⟶
                  (constantSheaf C.smallEtaleTopology AddCommGrpCat.{u}).obj
                    (ellPowerCoefficients.{u} ℓ n))),
              (∀ (W : FiniteEtale C) [PreGaloisCategory.IsConnected W] (m₀ m₁ : W ⟶ B)
                (t : ProCGroups.torsionLevel (G.AlgPoints hc K) Np),
                let s : W.left ⟶ Spec (.of K) := W.hom ≫ c
                let x : SchemeHomOver s (hD.divisionStructure
                    (P := algEquivZeroGroupCut c ⟨p, hp⟩) aj (Np : ℕ)) :=
                  ⟨m₀.left ≫ i, by
                    have hm : m₀.left ≫ B.hom = W.hom := m₀.w
                    have hprojection : (m₀.left ≫ i) ≫
                        hD.divisionProjection (P := algEquivZeroGroupCut c ⟨p, hp⟩) aj (Np : ℕ) =
                          W.hom :=
                      (Category.assoc _ _ _).trans
                        ((congrArg (fun f => m₀.left ≫ f) hi).trans hm)
                    exact (Category.assoc _ _ _).symm.trans
                      (congrArg (fun f => f ≫ c) hprojection)⟩
                let y : SchemeHomOver s (hD.divisionStructure
                    (P := algEquivZeroGroupCut c ⟨p, hp⟩) aj (Np : ℕ)) :=
                  ⟨m₁.left ≫ i, by
                    have hm : m₁.left ≫ B.hom = W.hom := m₁.w
                    have hprojection : (m₁.left ≫ i) ≫
                        hD.divisionProjection (P := algEquivZeroGroupCut c ⟨p, hp⟩) aj (Np : ℕ) =
                          W.hom :=
                      (Category.assoc _ _ _).trans
                        ((congrArg (fun f => m₁.left ≫ f) hi).trans hm)
                    exact (Category.assoc _ _ _).symm.trans
                      (congrArg (fun f => f ≫ c) hprojection)⟩
                let v : SchemeHomOver s (𝟙 (Spec (.of K))) := ⟨s, Category.comp_id s⟩
                postComp
                    (RelativeGroupLaw.UnitMultiplication.torsionPointSection G hc ⟨Np, hnK⟩ t) v =
                    hD.divisionDifference (P := algEquivZeroGroupCut c ⟨p, hp⟩) aj (Np : ℕ) x y →
                let x₀ := (finiteEtaleInclusion C).map m₀
                let y₀ := (finiteEtaleInclusion C).map m₁
                let l := pullback.lift x₀ y₀ (hT.hom_ext (x₀ ≫ q) (y₀ ≫ q))
                let edge := (freeAbelianSheafYoneda C.smallEtaleTopology).map l ≫
                  (freeCechEdgeSheafIso C.smallEtaleTopology q).inv ≫
                    abelianCechFirstRelationMap C.smallEtaleTopology hT q
                ∀ b : finiteLevelCohomology C ℓ n 1,
                  freeAbelianSheafYonedaHomEquiv C.smallEtaleTopology
                      ((finiteEtaleInclusion C).obj W)
                      ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{u}).obj
                        (ellPowerCoefficients.{u} ℓ n)) (edge ≫ d b) =
                    (toSheafify C.smallEtaleTopology ((Functor.const C.Etaleᵒᵖ).obj
                      (ellPowerCoefficients.{u} ℓ n))).app
                        (Opposite.op ((finiteEtaleInclusion C).obj W))
                      (ULift.up (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
                        (finiteLevelCup C ℓ n 1 1 2 rfl b
                          ((M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n).symm (τe.symm t)))))) →
              let cupSum : Ext.{u} A.X₁ F 1 := ∑ v ∈ S,
                finiteCechKernelCupClass Y ℓ n hTB qB
                  (finiteCechKernelPullback p₂ ℓ n hT q hq
                    (d (ellAdicProjection C ℓ 1 n v.2)))
                  (finiteLevelCohomologyPullback ℓ p₁ n 1 (ellAdicProjection C ℓ 1 n v.1))
              let aScaled := r.appr (n + 1) • aFinite
              (Ext.mk₀ (abelianCechFirstRelationMap Y.smallEtaleTopology hTB qB)).comp
                  aScaled (zero_add 1) =
                (Ext.mk₀ (abelianCechFirstRelationMap Y.smallEtaleTopology hTB qB)).comp
                  cupSum (zero_add 1) := by
  intro aj i hi algKC M hPrincipal Y p₁ p₂ cY z hz hL T hT q hq BC V eB cB hU hUI hVI
    hTB qB A F
    r S hS aμ hcoeff aFinite G hc Np hnK e hpoint τe hτe d hvalues cupSum aScaled
  classical
  have : IsNoetherian (finiteEtaleCoverOverlap B).left :=
    curveEtaleCoverOverlap_isNoetherian B c
  let hdom := curveEtaleCoverOverlap_stalk_isDomain B c
  apply abelianCechFirstRelation_ext_of_baseChange_components p₂ hT q hdom F 1
  intro Z j l edge
  let W := finiteEtaleCoverOverlapComponent B hdom Z
  have : PreGaloisCategory.IsConnected W := FiniteEtale.isConnected_of_connectedSpace_left W
  let m₀ := finiteEtaleCoverOverlapComponentFirst B hdom Z
  let m₁ := finiteEtaleCoverOverlapComponentSecond B hdom Z
  let WB := BC.obj ((finiteEtaleInclusion C).obj W)
  obtain ⟨t, ht, hroot⟩ := M.divisionRootDescent_exists_nativePicard_overlap
    ⟨p, hp⟩ D hD aj
    (fun x => by
      let xC : SchemeHomOver (𝟙 (Spec (.of K))) c := x
      have hclass := diagonalPicardClassifyingMap_fieldPointIso c p hp D hD K (𝟙 _) xC
      simp only [Category.id_comp] at hclass
      exact hclass)
    e hpoint ℓ hℓ n τe hτe B z hz W m₀ m₁ hTB qB aμ hcoeff
  let δ := (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n).symm (τe.symm t)
  have hvaluesW := hvalues W m₀ m₁ t ht
  let u₀ : WB ⟶ BC.obj ((finiteEtaleInclusion C).obj B) :=
    BC.map ((finiteEtaleInclusion C).map m₀)
  let u₁ : WB ⟶ BC.obj ((finiteEtaleInclusion C).obj B) :=
    BC.map ((finiteEtaleInclusion C).map m₁)
  have hNative : u₀ ≫ qB = u₁ ≫ qB := hTB.hom_ext _ _
  let nativeLift : WB ⟶ pullback qB qB := pullback.lift u₀ u₁ hNative
  let nativeEdge : (freeAbelianSheafYoneda Y.smallEtaleTopology).obj WB ⟶ A.X₁ :=
    (freeAbelianSheafYoneda Y.smallEtaleTopology).map nativeLift ≫
      (freeCechEdgeSheafIso Y.smallEtaleTopology qB).inv ≫
        abelianCechFirstRelationMap Y.smallEtaleTopology hTB qB
  have hEdge : nativeEdge = edge :=
    mapPullbackLift_postcomp_eq BC (freeAbelianSheafYoneda Y.smallEtaleTopology)
      q hTB ((finiteEtaleInclusion C).map m₀) ((finiteEtaleInclusion C).map m₁)
      (j ≫ pullback.fst q q) (j ≫ pullback.snd q q)
      (finiteEtaleCoverOverlapComponentFirst_inclusion B hdom Z)
      (finiteEtaleCoverOverlapComponentSecond_inclusion B hdom Z)
      (freeCechEdgeSheafIso Y.smallEtaleTopology qB).inv
      (abelianCechFirstRelationMap Y.smallEtaleTopology hTB qB)
  let R := finiteLevelCohomologyPresheafRestriction Y ℓ n WB 1
  let Φ : Ext.{u} A.X₁ F 1 →+ finiteLevelCohomology WB.left ℓ n 1 :=
    R.comp ((Ext.mk₀ edge).precomp F (zero_add 1))
  let restrictNative (a : Ext.{u} A.X₁ F 1) : finiteLevelCohomology WB.left ℓ n 1 :=
    R ((Ext.mk₀ nativeEdge).comp a (zero_add 1))
  have hΦ (a : Ext.{u} A.X₁ F 1) : Φ a = restrictNative a :=
    congrArg (fun k : (freeAbelianSheafYoneda Y.smallEtaleTopology).obj WB ⟶ A.X₁ =>
      R ((Ext.mk₀ k).comp a (zero_add 1))) hEdge.symm
  let v : finiteLevelCohomology WB.left ℓ n 1 :=
    finiteLevelCohomologyPullback ℓ (WB.hom ≫ p₁) n 1 δ
  have hrNative : restrictNative aFinite = v := hroot
  have hr : Φ aFinite = v := (hΦ aFinite).trans hrNative
  let proj (a : ellAdicCohomology C ℓ 1) : finiteLevelCohomology C ℓ n 1 :=
    ellAdicProjection C ℓ 1 n a
  let projM (a : ellAdicCohomology C ℓ 1) : finiteLevelCohomology C ℓ n 1 :=
    ellAdicProjection M.C ℓ 1 n a
  have hproj (a : ellAdicCohomology C ℓ 1) : proj a = projM a := rfl
  let cupTerm (a b : finiteLevelCohomology C ℓ n 1) : Ext.{u} A.X₁ F 1 :=
    finiteCechKernelCupClass Y ℓ n hTB qB
      (finiteCechKernelPullback p₂ ℓ n hT q hq (d b))
      (finiteLevelCohomologyPullback ℓ p₁ n 1 a)
  let cupSumNative : Ext.{u} A.X₁ F 1 := ∑ w ∈ S, cupTerm (projM w.1) (projM w.2)
  have hcupSum : cupSum = cupSumNative := by
    apply Finset.sum_congr rfl
    intro w _
    exact congrArg₂ cupTerm (hproj w.1) (hproj w.2)
  let x₀ := (finiteEtaleInclusion C).map m₀
  let y₀ := (finiteEtaleInclusion C).map m₁
  let liftC := pullback.lift x₀ y₀ (hT.hom_ext (x₀ ≫ q) (y₀ ≫ q))
  let edgeC := (freeAbelianSheafYoneda C.smallEtaleTopology).map liftC ≫
    (freeCechEdgeSheafIso C.smallEtaleTopology q).inv ≫
      abelianCechFirstRelationMap C.smallEtaleTopology hT q
  let F₀ := (constantSheaf C.smallEtaleTopology AddCommGrpCat.{u}).obj
    (ellPowerCoefficients.{u} ℓ n)
  let W₀ := (finiteEtaleInclusion C).obj W
  let value (a : finiteLevelCohomology C ℓ n 1) : F₀.obj.obj (Opposite.op W₀) :=
    freeAbelianSheafYonedaHomEquiv C.smallEtaleTopology W₀ F₀ (edgeC ≫ d a)
  let cupValue (a : finiteLevelCohomology C ℓ n 1) : F₀.obj.obj (Opposite.op W₀) :=
    (toSheafify C.smallEtaleTopology
      ((Functor.const C.Etaleᵒᵖ).obj (ellPowerCoefficients.{u} ℓ n))).app (Opposite.op W₀)
        (ULift.up (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
          (finiteLevelCup C ℓ n 1 1 2 rfl a δ)))
  have hsum : restrictNative cupSumNative = r • v :=
    M.diagonalDivisionCupSum_restriction ℓ hℓ r S hS n p₁ p₂ hT q hq x₀ y₀ d δ
      (fun w _ => by
        have hv : value (proj w.2) = cupValue (proj w.2) := hvaluesW (proj w.2)
        exact (congrArg value (hproj w.2).symm).trans
          (hv.trans (congrArg cupValue (hproj w.2))))
  have hcups : Φ cupSum = r • v :=
    (hΦ cupSum).trans ((congrArg restrictNative hcupSum).trans hsum)
  apply finiteLevelCohomologyPresheafRestriction_injective Y ℓ n WB 1
  change Φ (r.appr (n + 1) • aFinite) = Φ cupSum
  exact scaled_restriction_eq Φ (r.appr (n + 1)) aFinite cupSum v (r • v) hr hcups
    (finiteLevelCohomology_smul_eq_appr WB.left ℓ n 1 r v).symm

end AlgebraicCurve.CurveModel
