/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.JacobianVarieties.Kummer.ActualGenericWeilComparison
public import Nyll.AlgebraicCurves.Models.Kummer.DivisorClassCohomologyComparison
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Pic0EquivPointsPicardRepresentability
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
public import Nyll.JacobianVarieties.Kummer.CohomologyPullback
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericPointCharacterDetection
public import Nyll.EtaleFundamentalGroups.Cohomology.H1CharacterComposition
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitMonodromy
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.SchemeTheory.Normalization.Normal
public import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Actual Abel--Jacobi pullback of the Weil monodromy classes

The proved geometric Weil--Kummer identity identifies the actual derived H¹
pullback. Only the invertible multiplication index is used; there is no
characteristic-zero or full Tate-module requirement.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve NeronModelInfra GoodReductionJacobian
open EtaleFundamentalGroups.Cohomology
open JacobianVarieties.Picard.Proofs.Pic0PointsAbelJacobi.AlgebraicGeometry.RelPicard

namespace JacobianVarieties.Kummer

attribute [local instance] IsCurveOver.toHasPrincipalDivisors CurveModel.isIntegral

/-- The classes defined by the actual Weil multiplication character pull back
along the original Abel--Jacobi morphism to the original curve Kummer classes.
The character formula is supplied by `exists_jacobian_weil_cohomology`; the
pullback comparison is proved here from the original geometric construction. -/
theorem actual_abelJacobi_weil_cohomology_pullback
    {K F₀ : Type u} [Field K] [IsAlgClosed K]
    [Field F₀] [Algebra K F₀] [IsCurveOver K F₀]
    (M₀ : CurveModel K F₀)
    [Algebra K M₀.C.functionField]
    (hbase : algebraMap K M₀.C.functionField = baseToFunctionField M₀.toBase)
    {Ω F : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra M₀.C.functionField Ω] [IsScalarTower K M₀.C.functionField Ω]
    [Normal M₀.C.functionField Ω]
    [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    [Algebra F₀ F] [Algebra K F]
    [IsScalarTower K F₀ F] [IsScalarTower K Ω F]
    (hfg : ∃ t : F₀, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set F₀)) F₀)
    (hfg' : ∃ t : F, Transcendental Ω t ∧
      FiniteDimensional (IntermediateField.adjoin Ω ({t} : Set F)) F)
    (hgen : IntermediateField.adjoin Ω (Set.range (algebraMap F₀ F)) = ⊤)
    [IsProper M₀.toBase] [SmoothOfRelativeDimension 1 M₀.toBase] [GeometricallyIntegral M₀.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase)
    (D : RelativePic0Designation K M₀.toBase)
    (hD : RepresentsRelSubPic M₀.toBase ε (algEquivZeroCut M₀.toBase ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (aj : SchemeHomOver M₀.toBase D.toBase)
    (hclass : ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
      (x : SchemeHomOver t M₀.toBase),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M₀.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M₀.toBase (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (M : CurveModel Ω F) (eC : M.C ≅ pullback M₀.toBase (specMap K Ω))
    (heC : eC.hom ≫ pullback.snd M₀.toBase (specMap K Ω) = M.toBase)
    (hsq : ∀ (U : M₀.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme
          ((eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω)) ⁻¹ᵁ U))]
        (r : Γ(M₀.C, U)),
      M.ffEquiv.symm (M.C.germToFunctionField
        ((eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω)) ⁻¹ᵁ U)
        (((eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω)).app U).hom r)) =
      algebraMap F₀ F (M₀.ffEquiv.symm (M₀.C.germToFunctionField U r)))
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) :
    let : Algebra.EssFiniteType K F₀ := DictGlue.essFiniteType_of_curveModel M₀
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let : ConnectedSpace D.P :=
      GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
    let G := RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    let η := Spec.map (CommRingCat.ofHom (algebraMap M₀.C.functionField Ω))
    let q := M₀.C.fromSpecStalk (genericPoint M₀.C)
    let ξ := η ≫ q
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    ∀ (e₀ : Pic0 K F₀ ≃+ G.AlgPoints hc K)
      (τn : Pic0.torsion K F₀ (n : ℕ) ≃+
        ProCGroups.torsionLevel (G.AlgPoints hc K) n),
      (∀ t, (τn t).1 = e₀ t.1) →
      (∀ v : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase,
        ∃ Dv : Divisor.degZero (K := K) (F := F₀),
          (Dv : Divisor K F₀) = Finsupp.single (M₀.pointEquivPlace v) 1 -
            Finsupp.single (M₀.pointEquivPlace ε) 1 ∧
          (RelativeGroupLaw.AlgPoints.toPoint (e₀ (Pic0.mk Dv))).1 = v.1 ≫ aj.1) →
    ∀ (w : DivisorialWeilPairingData K F₀ (n : ℕ))
      (ν : Pic0.torsion K F₀ (n : ℕ) →+
        Sheaf.H.{u} ((constantSheaf D.P.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1),
      (∀ (x : Pic0.torsion K F₀ (n : ℕ))
        (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)),
        ((finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).1 (ν x)).toMul g :
          rootsOfUnity (n : ℕ) K).val.val =
            w.pair x (τn.symm
              (RelativeGroupLaw.UnitMultiplication.monodromy G hc ⟨n, hn⟩ g))) →
      ∀ a : Pic0.torsion K F₀ (n : ℕ),
        constantCohomologyPullback aj.1 A 1 (ν a) =
          M₀.kummerTorsionCohomology n hn ξ a := by
  intro hfinite A hconnected G hc η q ξ htop hdiscrete hAtop hAdiscrete
    e₀ τn hτn hpoint₀ w ν hν a
  classical
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  have : Smooth M₀.toBase := SmoothOfRelativeDimension.smooth 1 M₀.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M₀.C := IsNormalIntegral.of_stalks M₀.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M₀.toBase x).2)
  let τ := Classical.choice
    (FiniteEtale.nonempty_fiber_iso (η ≫ q ≫ aj.1) (G.one (𝟙 (Spec (.of K)))).1)
  let z := τ.inv.app (RelativeGroupLaw.UnitMultiplication.cover G hc ⟨n, hn⟩)
    (RelativeGroupLaw.UnitMultiplication.unit G hc ⟨n, hn⟩)
  obtain ⟨u, hu, hgeneric⟩ := exists_actual_abelJacobi_generic_weil_kummer
    M₀ hbase hfg hfg' hgen ε D hD aj hclass M eC heC hsq n hn w a
    e₀ τn hτn hpoint₀ τ z
  apply finiteH1_ext_genericFieldAction M₀.C Ω A
  intro σ
  let γ := toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M₀.C.functionField] Ω) σ
  let δ := FiniteEtale.fundamentalGroupHom q η γ
  have hchain := h1Character_pullback_fundamentalGroupHom_conj
    q aj.1 η (G.one (𝟙 (Spec (.of K)))).1 τ A (ν a) γ
  have hk : (finiteH1CharacterEquiv A ξ
      (M₀.kummerTorsionCohomology n hn ξ a)).toMul δ =
      M₀.kummerMonodromyCharacter n u hn ξ δ := by
    rw [← hu, M₀.kummerTorsionCohomology_kummerClass]
    change ((finiteH1CharacterEquiv A ξ)
      ((finiteH1CharacterEquiv A ξ).symm
        (Additive.ofMul (M₀.kummerMonodromyCharacter n u hn ξ)))).toMul δ = _
    rw [AddEquiv.apply_symm_apply]
    rfl
  rw [hk]
  apply Subtype.ext
  apply Units.ext
  exact (congrArg (fun ζ : rootsOfUnity (n : ℕ) K => ζ.val.val) hchain).trans
    ((hν a _).trans (hgeneric σ))

end JacobianVarieties.Kummer
