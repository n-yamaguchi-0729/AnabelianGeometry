/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.JacobianVarieties.Kummer.ActualWeilCohomologyPullback
public import Nyll.JacobianVarieties.Kummer.JacobianWeilCharacters
public import Nyll.JacobianVarieties.Kummer.JacobianWeilCohomologyBijective
public import Nyll.AlgebraicCurves.Models.Kummer.DivisorClassCohomologyComparison
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Pic0EquivPointsPicardRepresentability
public import Nyll.JacobianVarieties.Kummer.CohomologyPullbackCharacters

/-!
# Actual Abel--Jacobi pullback on finite-coefficient H¹

The geometric generic Weil--Kummer identity determines the actual global
derived-cohomology pullback. The auxiliary geometric model is supplied here
with its germ and field-generation data; construction of this model is separate.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve NeronModelInfra GoodReductionJacobian
open EtaleFundamentalGroups.Cohomology

namespace JacobianVarieties.Kummer

open JacobianVarieties.Picard.Proofs.Pic0PointsAbelJacobi.AlgebraicGeometry.RelPicard

attribute [local instance] IsCurveOver.toHasPrincipalDivisors

/-- For the actual Abel--Jacobi morphism, pullback on finite constant
roots-of-unity H¹ is bijective, by the proved geometric generic comparison. -/
theorem actual_abelJacobi_finiteH1Pullback_bijective
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
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let : ConnectedSpace D.P :=
      GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
    Function.Bijective (constantCohomologyPullback aj.1 A 1) := by
  intro A hconnected
  classical
  have : Algebra.EssFiniteType K F₀ := DictGlue.essFiniteType_of_curveModel M₀
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  let G := RepresentsRelSubPic.relativeGroupLaw
    (P := algEquivZeroGroupCut M₀.toBase ε) hD
  let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
    (P := algEquivZeroGroupCut M₀.toBase ε) hD
  let η := Spec.map (CommRingCat.ofHom (algebraMap M₀.C.functionField Ω))
  let q := M₀.C.fromSpecStalk (genericPoint M₀.C)
  let ξ := η ≫ q
  obtain ⟨e₀, hpoint₀, τn, hτn, _, w, ν, hν⟩ :=
    exists_jacobian_weil_cohomology M₀ ε D hD aj hclass n hn
  have hνbij := jacobian_weil_cohomology_bijective_of_isUnit hfg G hc n hn τn w ν hν
  have hcompare := actual_abelJacobi_weil_cohomology_pullback
    M₀ hbase hfg hfg' hgen ε D hD aj hclass M eC heC hsq n hn
    e₀ τn hτn hpoint₀ w ν hν
  have hκbij := (M₀.kummerTorsionCohomologyEquiv n hn ξ).bijective
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := hνbij.2 x
    obtain ⟨b, rfl⟩ := hνbij.2 y
    have hab : a = b := hκbij.1
      ((hcompare a).symm.trans (hxy.trans (hcompare b)))
    exact congrArg ν hab
  · intro y
    obtain ⟨a, ha⟩ := hκbij.2 y
    exact ⟨ν a, (hcompare a).trans ha⟩

end JacobianVarieties.Kummer
