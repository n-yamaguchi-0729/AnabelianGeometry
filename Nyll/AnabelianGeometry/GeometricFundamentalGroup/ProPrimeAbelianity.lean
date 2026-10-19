/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.ProPrimePowerCover
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.AbelianityClassification
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.ProperCoverH1Degree
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.OpenCoverH1Numerics
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualEquivalence
import Mathlib.Tactic.Linarith

/-! # Abelian maximal pro-prime fundamental groups

A single prime detects precisely the four nonhyperbolic curve types. In
the hyperbolic cases, the actual power-image cover constructed from an
abelian maximal quotient would have nonincreasing prime-order H¹, whereas
its actual Riemann--Hurwitz formula forces a strict increase.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open ProCGroups ProCGroups.ProC
open scoped IsMulCommutative

namespace AnabelianGeometry.GeometricFundamentalGroup

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

private theorem not_isMulCommutative_maximalProP_proper_hyperbolic
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F) (hg : 2 ≤ genusFF K F)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ M.C)
    (p : ℕ) [Fact p.Prime] :
    ¬ IsMulCommutative
      (π₁ᵉᵗ(xi) ⧸ proCResidualCore (FiniteGroupClass.pGroup p) π₁ᵉᵗ(xi)) := by
  intro hcomm
  have hp : p.Prime := Fact.out
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  have : GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  have hcard := M.natCard_finiteH1_eq_pow_genus ε ⟨p, hp.pos⟩ xi
  have hn : 1 < Nat.card (Sheaf.H.{0}
      ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity p K)))) 1) := by
    exact (Nat.one_lt_pow (by omega) hp.one_lt).trans_le hcard.ge
  obtain ⟨W, hW, xiW, _hxiW, hdegree, hle⟩ :=
    exists_galoisCover_finiteH1_card_le_of_abelian_maximalProP K xi p hn hcomm
  have : IsGalois W := hW
  obtain ⟨q, hqcard, hRH⟩ := exists_finiteH1_exponent_proper_cover M W xi xiW ⟨p, hp.pos⟩
  have hlePow := hqcard.ge.trans (hle.trans hcard.le)
  have hq : q ≤ 2 * genusFF K F := by
    by_contra h
    exact (not_lt_of_ge hlePow) (Nat.pow_lt_pow_right hp.one_lt (by omega))
  have hgZ : (2 : ℤ) ≤ genusFF K F := by exact_mod_cast hg
  have hdZ : (1 : ℤ) < Nat.card ((fiber xi).obj W) := by exact_mod_cast hdegree
  have hqZ : (q : ℤ) ≤ 2 * (genusFF K F : ℤ) := by exact_mod_cast hq
  nlinarith

private theorem not_isMulCommutative_maximalProP_open_hyperbolic
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F)
    {X : Scheme} [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (hboundary : (M.openBoundaryPlaces j).Nonempty)
    (hhyper : 0 < 2 * (genusFF K F : ℤ) + Nat.card (M.openBoundaryPlaces j) - 2)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    (p : ℕ) [Fact p.Prime] :
    ¬ IsMulCommutative
      (π₁ᵉᵗ(xi) ⧸ proCResidualCore (FiniteGroupClass.pGroup p) π₁ᵉᵗ(xi)) := by
  classical
  intro hcomm
  have hp : p.Prime := Fact.out
  let : Fintype (M.openBoundaryPlaces j) := (M.openBoundaryPlaces_finite j).fintype
  have hr : 0 < Nat.card (M.openBoundaryPlaces j) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr hboundary.to_subtype
  let d := 2 * genusFF K F + (Nat.card (M.openBoundaryPlaces j) - 1)
  have hd : (d : ℤ) - 1 =
      2 * (genusFF K F : ℤ) + Nat.card (M.openBoundaryPlaces j) - 2 := by
    dsimp only [d]
    omega
  have hcard := natCard_finiteH1_eq_pow_genus_boundary M j ⟨p, hp.pos⟩ xi
  have hn : 1 < Nat.card (Sheaf.H.{0}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity p K)))) 1) := by
    exact (Nat.one_lt_pow (by omega) hp.one_lt).trans_le hcard.ge
  obtain ⟨W, hW, xiW, hxiW, hdegree, hle⟩ :=
    exists_galoisCover_finiteH1_card_le_of_abelian_maximalProP K xi p hn hcomm
  have : IsGalois W := hW
  obtain ⟨q, hqcard, hRH⟩ :=
    exists_openCover_finiteH1_exponent M j hboundary W ⟨p, hp.pos⟩ xi xiW hxiW
  have hlePow := hqcard.ge.trans (hle.trans hcard.le)
  have hq : q ≤ d := by
    by_contra h
    exact (not_lt_of_ge hlePow) (Nat.pow_lt_pow_right hp.one_lt (by omega))
  have hdZ : (1 : ℤ) < Nat.card ((fiber xi).obj W) := by exact_mod_cast hdegree
  have hqZ : (q : ℤ) ≤ d := by exact_mod_cast hq
  nlinarith

/-- For every prime p, the actual maximal pro-p geometric fundamental
 group is abelian exactly in types (0,0), (0,1), (0,2), and (1,0).
No presentation or condition on covering subgroups is supplied. -/
theorem isMulCommutative_maximalProP_iff
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F) (U : M.C.Opens)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ U.toScheme)
    (p : ℕ) [Fact p.Prime] :
    IsMulCommutative
        (π₁ᵉᵗ(xi) ⧸ proCResidualCore (FiniteGroupClass.pGroup p) π₁ᵉᵗ(xi)) ↔
      (genusFF K F = 0 ∧ Nat.card (M.openBoundaryPlaces U.ι) ≤ 2) ∨
      (genusFF K F = 1 ∧ Nat.card (M.openBoundaryPlaces U.ι) = 0) := by
  classical
  have : Nonempty U := ⟨xi (IsLocalRing.closedPoint Ω)⟩
  have : IsIntegral U.toScheme := inferInstance
  have : IsLocallyNoetherian M.C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  have : CompactSpace M.C := QuasiCompact.compactSpace_of_compactSpace M.toBase
  have : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace U.ι
  constructor
  · intro hcomm
    by_contra hsmall
    by_cases hr : Nat.card (M.openBoundaryPlaces U.ι) = 0
    · have hg : 2 ≤ genusFF K F := by omega
      have : IsIso U.ι := isIso_of_openBoundary_card_eq_zero M U.ι hr
      let E : FiniteEtale M.C ≌ FiniteEtale U.toScheme :=
        MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤
          (asIso U.ι).symm
      have : (pullback U.ι).IsEquivalence := E.isEquivalence_functor
      let e := residualQuotientContinuousMulEquiv (FiniteGroupClass.pGroup_hereditary p)
        (fundamentalGroupEquivOfPullbackEquivalence U.ι xi)
      have : IsMulCommutative
          (π₁ᵉᵗ(xi) ⧸ proCResidualCore (FiniteGroupClass.pGroup p) π₁ᵉᵗ(xi)) := hcomm
      have hc : IsMulCommutative
          (π₁ᵉᵗ(xi ≫ U.ι) ⧸ proCResidualCore (FiniteGroupClass.pGroup p) π₁ᵉᵗ(xi ≫ U.ι)) :=
        ⟨⟨fun a b => e.symm.injective
          ((e.symm.map_mul a b).trans ((mul_comm (e.symm a) (e.symm b)).trans
            (e.symm.map_mul b a).symm))⟩⟩
      exact not_isMulCommutative_maximalProP_proper_hyperbolic M hg (xi ≫ U.ι) p hc
    · have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
      have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
        (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
      have : IsNormalIntegral U.toScheme := IsNormalIntegral.of_stalks U.toScheme
        (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk (U.ι ≫ M.toBase) x).2)
      let : Fintype (M.openBoundaryPlaces U.ι) := (M.openBoundaryPlaces_finite U.ι).fintype
      have hpos : 0 < Fintype.card (M.openBoundaryPlaces U.ι) := by
        rw [← Nat.card_eq_fintype_card]
        omega
      obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpos
      have hhyper : 0 < 2 * (genusFF K F : ℤ) + Nat.card (M.openBoundaryPlaces U.ι) - 2 := by
        omega
      exact not_isMulCommutative_maximalProP_open_hyperbolic M U.ι
        ⟨v.val, v.property⟩ hhyper xi p hcomm
  · intro hsmall
    have : IsMulCommutative π₁ᵉᵗ(xi) :=
      (isMulCommutative_fundamentalGroup_iff M U xi).mpr hsmall
    infer_instance

end AnabelianGeometry.GeometricFundamentalGroup
