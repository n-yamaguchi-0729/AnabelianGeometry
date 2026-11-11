/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
public import Nyll.AlgebraicCurves.Models.Kummer.CurveNativeH1Picard
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechOverlap
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Sites.GaloisSections
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1CechKernel
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericPointCharacterDetection
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerPowerCoefficients
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
public import Nyll.JacobianVarieties.Kummer.CurveFiniteCupWeil
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Degree
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionFiniteCharacter
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionMonodromy
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.SchemeTheory.Normalization.Normal
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.CategoryTheory.Galois.Prorepresentability
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Original finite cup coefficients on the actual division overlaps

Every original finite H¹ class has a first-kernel representative on the
retained division cover. On each connected finite overlap its coefficient
is the degree of the original cup with the actual constant division
difference. The proof keeps the original covering points, the original
coherent roots, and the same Picard and torsion coordinates. In particular
the coefficient has the order `(class, division difference)`.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian EtaleCohomology EtaleCohomology.Classical
open EtaleFundamentalGroups.Cohomology

namespace JacobianVarieties.Kummer

/-- On the actual retained division cover, original finite H¹ classes
have original covering-kernel representatives whose overlap coefficients
are the original native cup degrees. The Picard coordinates are retained
to identify the same actual transition line bundle. -/
theorem exists_diagonalDivision_nativeCupKernels
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) c)
    (D : RelativePic0Designation K c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (aj : SchemeHomOver c D.toBase)
    (hclass : ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
      (x : SchemeHomOver t c),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
    (Y : FiniteEtale C) [IsConnected Y] [Surjective Y.hom]
    (i : Y.left ⟶ hD.divisionPullback (P := algEquivZeroGroupCut c ε)
      aj (ℓ ^ (n + 1)))
    (hi : i ≫ hD.divisionProjection (P := algEquivZeroGroupCut c ε)
      aj (ℓ ^ (n + 1)) = Y.hom) :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    let M := literalCurveModel c
    let _ : HasPrincipalDivisors K C.functionField :=
      (literalCurveModel_functionField_properties c).1.toHasPrincipalDivisors
    let N : ℕ+ := ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos (n + 1)⟩
    let hn : IsUnit ((N : ℕ) : K) := by
      change IsUnit ((ℓ ^ (n + 1) : ℕ) : K)
      simpa only [Nat.cast_pow] using hℓ.pow (n + 1)
    let G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
    let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut c ε) hD
    let A := ellPowerCoefficients.{u} ℓ n
    let T : C.Etale := Scheme.Etale.mk (𝟙 C)
    let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) C
    let q := finiteEtaleCoverBaseMap C Y
    let hq := finiteEtaleCoverBaseMap_covering C Y
    let S := abelianCechAugmentationSequence C.smallEtaleTopology hT q
    let hS := abelianCechAugmentationSequence_shortExact C.smallEtaleTopology hT q hq
    let F := (constantSheaf C.smallEtaleTopology AddCommGrpCat.{u}).obj A
    ∃ e : Pic0 K C.functionField ≃+ G.AlgPoints hc K,
      (∀ x : SchemeHomOver (𝟙 (Spec (.of K))) c,
        ∃ Dv : Divisor.degZero (K := K) (F := C.functionField),
          (Dv : Divisor K C.functionField) = Finsupp.single (M.pointEquivPlace x) 1 -
            Finsupp.single (M.pointEquivPlace ε) 1 ∧
          (RelativeGroupLaw.AlgPoints.toPoint (e (Pic0.mk Dv))).1 = x.1 ≫ aj.1) ∧
      ∃ τ : Pic0.torsion K C.functionField (ℓ ^ (n + 1)) ≃+
          ProCGroups.torsionLevel (G.AlgPoints hc K) N,
        (∀ x, (τ x).1 = e x.1) ∧
        (∀ x, (G.torsionLevelEquivSchemeKerPoints hc N (τ x)).1 ≫
          pullback.fst (G.schemeNsmul (N : ℕ)) (G.one (𝟙 (Spec (.of K)))).1 =
            (RelativeGroupLaw.AlgPoints.toPoint (e x.1)).1) ∧
        ∃ d : finiteLevelCohomology C ℓ n 1 → (S.X₁ ⟶ F),
          (∀ y, hS.extClass.comp (Abelian.Ext.mk₀ (d y)) (add_zero 1) = y) ∧
          ∀ (W : FiniteEtale C) [IsConnected W] (m₀ m₁ : W ⟶ Y)
            (t : ProCGroups.torsionLevel (G.AlgPoints hc K) N),
            let s : W.left ⟶ Spec (.of K) := W.hom ≫ c
            let x : SchemeHomOver s (hD.divisionStructure
                (P := algEquivZeroGroupCut c ε) aj (N : ℕ)) :=
              ⟨m₀.left ≫ i, by
                have hm : m₀.left ≫ Y.hom = W.hom := m₀.w
                have hprojection : (m₀.left ≫ i) ≫
                    hD.divisionProjection (P := algEquivZeroGroupCut c ε) aj (N : ℕ) =
                      W.hom :=
                  (Category.assoc _ _ _).trans
                    ((congrArg (fun f => m₀.left ≫ f) hi).trans hm)
                exact (Category.assoc _ _ _).symm.trans
                  (congrArg (fun f => f ≫ c) hprojection)⟩
            let y : SchemeHomOver s (hD.divisionStructure
                (P := algEquivZeroGroupCut c ε) aj (N : ℕ)) :=
              ⟨m₁.left ≫ i, by
                have hm : m₁.left ≫ Y.hom = W.hom := m₁.w
                have hprojection : (m₁.left ≫ i) ≫
                    hD.divisionProjection (P := algEquivZeroGroupCut c ε) aj (N : ℕ) =
                      W.hom :=
                  (Category.assoc _ _ _).trans
                    ((congrArg (fun f => m₁.left ≫ f) hi).trans hm)
                exact (Category.assoc _ _ _).symm.trans
                  (congrArg (fun f => f ≫ c) hprojection)⟩
            let v : SchemeHomOver s (𝟙 (Spec (.of K))) := ⟨s, Category.comp_id s⟩
            postComp (RelativeGroupLaw.UnitMultiplication.torsionPointSection G hc ⟨N, hn⟩ t) v =
                hD.divisionDifference (P := algEquivZeroGroupCut c ε) aj (N : ℕ) x y →
            let x₀ := (finiteEtaleInclusion C).map m₀
            let y₀ := (finiteEtaleInclusion C).map m₁
            let l := pullback.lift x₀ y₀ (hT.hom_ext (x₀ ≫ q) (y₀ ≫ q))
            let edge := (freeAbelianSheafYoneda C.smallEtaleTopology).map l ≫
              (freeCechEdgeSheafIso C.smallEtaleTopology q).inv ≫
                abelianCechFirstRelationMap C.smallEtaleTopology hT q
            ∀ b : finiteLevelCohomology C ℓ n 1,
              freeAbelianSheafYonedaHomEquiv C.smallEtaleTopology
                  ((finiteEtaleInclusion C).obj W) F (edge ≫ d b) =
                (toSheafify C.smallEtaleTopology ((Functor.const C.Etaleᵒᵖ).obj A)).app _
                  (ULift.up (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
                    (finiteLevelCup C ℓ n 1 1 2 rfl b
                      ((M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n).symm (τ.symm t))))) := by
  intro algKF M hprincipal N hn G hc A T hT q hq S hS F
  classical
  have : IsCurveOver K C.functionField := (literalCurveModel_functionField_properties c).1
  have : GeometricallyIntegral M.toBase := inferInstanceAs (GeometricallyIntegral c)
  have : ConnectedSpace D.P :=
    GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
  have : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral C := IsNormalIntegral.of_stalks C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk c x).2)
  let Ω := AlgebraicClosure C.functionField
  let η := Spec.map (CommRingCat.ofHom (algebraMap C.functionField Ω))
  let j := C.fromSpecStalk (genericPoint C)
  let ξ := η ≫ j
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  let : TopologicalSpace (Multiplicative A) := ⊥
  obtain ⟨e, hpoint, τ, hτ, hker, w, hformula, hstab⟩ :=
    exists_diagonalDivision_finiteLevelCharacters M ε D hD aj hclass ℓ hℓ n Y i hi
  let zY : (FiniteEtale.fiber ξ).obj Y := Classical.choice inferInstance
  have hd (b : finiteLevelCohomology C ℓ n 1) :=
    exists_h1_cechKernel_of_stabilizer A ξ Y zY hT q hq b (hstab b zY)
  choose d hclassd hvalues using hd
  refine ⟨e, hpoint, τ, hτ, hker, d, hclassd, ?_⟩
  intro W hW m₀ m₁ t s x y v hconstant x₀ y₀ l edge b
  let zW : (FiniteEtale.fiber ξ).obj W := Classical.choice inferInstance
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut (FiniteEtale.fiber ξ))
    ((FiniteEtale.fiber ξ).map m₀ zW) ((FiniteEtale.fiber ξ).map m₁ zW)
  obtain ⟨σ, rfl⟩ := FiniteEtale.genericFieldAction_surjective C Ω g
  let γ := toAut (FiniteEtale.fiber η) (Ω ≃ₐ[C.functionField] Ω) σ
  let path := Classical.choice
    (FiniteEtale.nonempty_fiber_iso (η ≫ j ≫ aj.1) (G.one (𝟙 (Spec (.of K)))).1)
  have hmon := divisionGenericMonodromy_eq_of_constant_difference
    (P := algEquivZeroGroupCut c ε) hD aj N hn Y i hi W m₀ m₁ path σ zW t
      hconstant hg
  have hv := hvalues b W m₀ m₁ zW (FiniteEtale.fundamentalGroupHom j η γ) hg.symm
  have hscalar : (h1Character A ξ b (FiniteEtale.fundamentalGroupHom j η γ)).toAdd =
      ULift.up (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
        (finiteLevelCup C ℓ n 1 1 2 rfl b
          ((M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n).symm (τ.symm t)))) := by
    apply (ellPowerRootsCoefficientEquiv K ℓ hℓ n).injective
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    have hchar := hformula b path σ
    have hmonPair := congrArg
      (fun z : ProCGroups.torsionLevel (G.AlgPoints hc K) N =>
        w.pair (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n b) (τ.symm z)) hmon
    have hcup := CurveModel.nativeFiniteCup_eq_divisorialWeilPairing c ℓ hℓ n w b
      ((M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n).symm (τ.symm t))
    have hcupCoordinate := congrArg
      (w.pair (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n b))
      ((M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n).apply_symm_apply (τ.symm t))
    exact (hchar.trans hmonPair).trans (hcup.trans hcupCoordinate).symm
  exact hv.trans (congrArg
    ((toSheafify C.smallEtaleTopology ((Functor.const C.Etaleᵒᵖ).obj A)).app _) hscalar)

end JacobianVarieties.Kummer
