/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.ActualGenericWeilComparison
import Nyll.JacobianVarieties.Kummer.SemilinearGenericCharacter
import Nyll.JacobianVarieties.WeilPairing.CharZeroNondegeneracy
import Nyll.JacobianVarieties.WeilPairing.DivisorialPairingPairSemilinearSmul

/-!
# Semilinear naturality of actual Abel--Jacobi multiplication monodromy

The existing generic Weil--Kummer comparison and the semilinear Kummer
character formula determine the actual finite multiplication monodromy.
A single specified Picard/points comparison is retained throughout.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Kummer

open JacobianVarieties.Picard.Proofs.Pic0PointsAbelJacobi.AlgebraicGeometry.RelPicard

attribute [local instance] IsCurveOver.toHasPrincipalDivisors

/-- The actual Abel--Jacobi multiplication monodromy is semilinear in the
torsion coordinates of the same specified Picard/points comparison. -/
theorem actual_abelJacobi_generic_monodromy_semilinear
    {K F₀ : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F₀] [Algebra K F₀] [IsCurveOver K F₀]
    (M₀ : CurveModel K F₀)
    [Algebra K M₀.C.functionField]
    (hbase : algebraMap K M₀.C.functionField = baseToFunctionField M₀.toBase)
    {Ω F : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra M₀.C.functionField Ω] [IsScalarTower K M₀.C.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M₀.C.functionField Ω]
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
    (hclass : ∀ (L : Type) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
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
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    (w : DivisorialWeilPairingData K F₀ (n : ℕ)) :
    let G := RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    let η := Spec.map (CommRingCat.ofHom (algebraMap M₀.C.functionField Ω))
    let q := M₀.C.fromSpecStalk (genericPoint M₀.C)
    ∀ (e₀ : Pic0 K F₀ ≃+ G.AlgPoints hc K)
      (τn : Pic0.torsion K F₀ (n : ℕ) ≃+
        ProCGroups.torsionLevel (G.AlgPoints hc K) n),
      (∀ t, (τn t).1 = e₀ t.1) →
      (∀ v : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase,
        ∃ Dv : Divisor.degZero (K := K) (F := F₀),
          (Dv : Divisor K F₀) = Finsupp.single (M₀.pointEquivPlace v) 1 -
            Finsupp.single (M₀.pointEquivPlace ε) 1 ∧
          (RelativeGroupLaw.AlgPoints.toPoint (e₀ (Pic0.mk Dv))).1 = v.1 ≫ aj.1) →
    ∀ (b : FiniteEtale.fiber (η ≫ q ≫ aj.1) ≅
        FiniteEtale.fiber (G.one (𝟙 (Spec (.of K)))).1)
      (_z : (FiniteEtale.fiber (η ≫ q ≫ aj.1)).obj (G.multiplicationCover hc n))
      (g : SemilinearAut K F₀) (φ : M₀.C.functionField ≃+* M₀.C.functionField)
      (_hφ : ∀ r : F₀, φ (M₀.ffEquiv r) = M₀.ffEquiv (SemilinearAut.toRingAut g r))
      (a : Ω ≃+* Ω)
      (ha : ∀ r : M₀.C.functionField,
        a (algebraMap M₀.C.functionField Ω r) = algebraMap M₀.C.functionField Ω (φ r))
      (σ : Ω ≃ₐ[M₀.C.functionField] Ω),
      τn.symm (G.multiplicationMonodromy hc n
        (continuousConjAut b (FiniteEtale.fundamentalGroupHom (q ≫ aj.1) η
          (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M₀.C.functionField] Ω)
            (KummerTheory.semilinearGaloisConjugate φ a ha σ))))) =
        g • τn.symm (G.multiplicationMonodromy hc n
          (continuousConjAut b (FiniteEtale.fundamentalGroupHom (q ≫ aj.1) η
            (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M₀.C.functionField] Ω) σ)))) := by
  intro G hc η q e₀ τn hτn hpoint b z g φ hφ a ha σ
  have : Algebra.EssFiniteType K F₀ := DictGlue.essFiniteType_of_curveModel M₀
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let s := fun ρ : Ω ≃ₐ[M₀.C.functionField] Ω =>
    FiniteEtale.fundamentalGroupHom q η
      (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M₀.C.functionField] Ω) ρ)
  let t := fun ρ : Ω ≃ₐ[M₀.C.functionField] Ω =>
    τn.symm (G.multiplicationMonodromy hc n
      (continuousConjAut b (FiniteEtale.fundamentalGroupHom (q ≫ aj.1) η
        (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M₀.C.functionField] Ω) ρ))))
  have hpair (x : Pic0.torsion K F₀ n) (ρ : Ω ≃ₐ[M₀.C.functionField] Ω) :
      w.pair x (t ρ) =
        ((M₀.kummerTorsionCharacter n hn (η ≫ q) (Multiplicative.ofAdd x) (s ρ) :
          Kˣ) : K) := by
    obtain ⟨u, hu, hgeneric⟩ := exists_actual_abelJacobi_generic_weil_kummer
      M₀ hbase hfg hfg' hgen ε D hD aj hclass M eC heC hsq n hn w x
      e₀ τn hτn hpoint b z
    have hu' : Pic0.kummerClass n u = Multiplicative.ofAdd x :=
      congrArg Multiplicative.ofAdd hu
    rw [← hu', M₀.kummerTorsionCharacter_kummerClass]
    exact hgeneric ρ
  have heq (x : Pic0.torsion K F₀ n) :
      w.pair (g • x) (t (KummerTheory.semilinearGaloisConjugate φ a ha σ)) =
        w.pair (g • x) (g • t σ) := by
    rw [w.pair_semilinearSmul, hpair, hpair]
    exact M₀.kummerTorsionCharacter_generic_semilinear n hn g φ hφ a ha x σ
  change t (KummerTheory.semilinearGaloisConjugate φ a ha σ) = g • t σ
  apply w.toHom_injective_charZero hfg
  apply Additive.toMul.injective
  ext x
  change w.pair (t (KummerTheory.semilinearGaloisConjugate φ a ha σ)) x =
    w.pair (g • t σ) x
  rw [w.pair_swap_eq_inv x, w.pair_swap_eq_inv x]
  congr 1
  simpa only [smul_inv_smul] using heq (g⁻¹ • x)

end JacobianVarieties.Kummer
