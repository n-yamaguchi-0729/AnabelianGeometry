/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.TrivialityClassification
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentProfiniteIntegers
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.ProperCurveSlim
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.OpenCurveSlim
import Nyll.JacobianVarieties.Albanese.GenusOneAbelJacobiIsomorphism
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianTateComparison

/-! # The actual curves with abelian geometric fundamental group -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.FiniteEtale
open ProCGroups.FiniteStepSolvableQuotients
open scoped IsMulCommutative

namespace AnabelianGeometry.GeometricFundamentalGroup

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

private theorem subsingleton_of_slim_commutative
    {G : Type*} [Group G] [TopologicalSpace G] (hslim : IsSlim G)
    (hcomm : ∀ a b : G, a * b = b * a) : Subsingleton G := by
  have hcenter := center_eq_bot_of_isSlim hslim
  have hone (g : G) : g = 1 := by
    have hg : g ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr (fun a => hcomm a g)
    rw [hcenter] at hg
    exact Subgroup.mem_bot.mp hg
  exact ⟨fun a b => (hone a).trans (hone b).symm⟩

/-- A genus-one proper curve has abelian fundamental group. The actual
Abel--Jacobi isomorphism and full Tate comparison are constructed internally. -/
theorem isMulCommutative_fundamentalGroup_of_genus_one
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F) (hg : genusFF K F = 1)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ M.C) :
    IsMulCommutative π₁ᵉᵗ(xi) := by
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  obtain ⟨D, hD, aj, hs, hp, hc, _hzero, hiso⟩ :=
    M.exists_abelJacobi_isIso_of_genus_one hg ε
  have : Smooth D.toBase := hs
  have : IsProper D.toBase := hp
  have : GeometricallyConnected D.toBase := hc
  have : ConnectedSpace D.P :=
    GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
  have : IsIso aj.1 := hiso
  let G := RepresentsRelSubPic.relativeGroupLaw
    (P := algEquivZeroGroupCut M.toBase ε) hD
  let hcomm : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
    (P := algEquivZeroGroupCut M.toBase ε) hD
  let E : FiniteEtale D.P ≌ FiniteEtale M.C :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤
      (asIso aj.1).symm
  have : (pullback aj.1).IsEquivalence := E.isEquivalence_functor
  let e := (fundamentalGroupEquivOfPullbackEquivalence aj.1 xi).trans
    (G.fundamentalGroupEquivFullTateAt hcomm (xi ≫ aj.1))
  exact ⟨⟨fun a b => e.injective
    ((e.map_mul a b).trans ((mul_comm (e a) (e b)).trans (e.map_mul b a).symm))⟩⟩

/-- The full geometric fundamental group is abelian exactly for the four
nonhyperbolic types: (0,0), (0,1), (0,2), and (1,0). No presentation,
rational coordinates, point on the compactification, or group law is input. -/
theorem isMulCommutative_fundamentalGroup_iff
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F) (U : M.C.Opens)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ U.toScheme) :
    IsMulCommutative π₁ᵉᵗ(xi) ↔
      (genusFF K F = 0 ∧ Nat.card (M.openBoundaryPlaces U.ι) ≤ 2) ∨
      (genusFF K F = 1 ∧ Nat.card (M.openBoundaryPlaces U.ι) = 0) := by
  classical
  have : Nonempty U := ⟨xi (IsLocalRing.closedPoint Ω)⟩
  have : IsIntegral U.toScheme := inferInstance
  have : IsLocallyNoetherian M.C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  have : CompactSpace M.C := QuasiCompact.compactSpace_of_compactSpace M.toBase
  have : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace U.ι
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  have : Algebra.EssFiniteType K F := by
    let : Algebra K M.C.functionField := M.functionFieldAlgebra
    exact (Algebra.EssFiniteType.iff_of_algEquiv M.ffAlgEquiv).mpr
      (essFiniteType_functionField M.toBase)
  constructor
  · intro hcomm
    have : IsMulCommutative π₁ᵉᵗ(xi) := hcomm
    by_contra hsmall
    have htrivial : Subsingleton π₁ᵉᵗ(xi) := by
      by_cases hr : Nat.card (M.openBoundaryPlaces U.ι) = 0
      · have hg : 2 ≤ genusFF K F := by omega
        have : IsIso U.ι := isIso_of_openBoundary_card_eq_zero M U.ι hr
        let E : FiniteEtale M.C ≌ FiniteEtale U.toScheme :=
          MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤
            (asIso U.ι).symm
        have : (pullback U.ι).IsEquivalence := E.isEquivalence_functor
        let e := fundamentalGroupEquivOfPullbackEquivalence U.ι xi
        have hc : ∀ a b : π₁ᵉᵗ(xi ≫ U.ι), a * b = b * a := by
          intro a b
          apply e.symm.injective
          rw [map_mul, map_mul]
          exact mul_comm _ _
        have ht := subsingleton_of_slim_commutative
          (isSlim_fundamentalGroup_proper_hyperbolic M hg (xi ≫ U.ι)) hc
        exact ⟨fun a b => e.injective (ht.elim (e a) (e b))⟩
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
        have hhyper : 0 < 2 * (genusFF K F : ℤ) +
            (M.openBoundaryPlaces_finite U.ι).toFinset.card - 2 := by
          rw [Set.Finite.card_toFinset, ← Nat.card_eq_fintype_card]
          omega
        exact subsingleton_of_slim_commutative
          (isSlim_fundamentalGroup_open_hyperbolic M U.ι ⟨v.val, v.property⟩ hhyper xi)
          (fun a b => mul_comm a b)
    obtain ⟨hg, hr⟩ :=
      (subsingleton_fundamentalGroup_iff_genus_zero_boundary_le_one M U xi).mp htrivial
    exact hsmall (Or.inl ⟨hg, by omega⟩)
  · rintro (⟨hg, hr⟩ | ⟨hg, hr⟩)
    · by_cases hsmall : Nat.card (M.openBoundaryPlaces U.ι) ≤ 1
      · have htrivial :=
          (subsingleton_fundamentalGroup_iff_genus_zero_boundary_le_one M U xi).mpr ⟨hg, hsmall⟩
        exact ⟨⟨fun a b => htrivial.elim (a * b) (b * a)⟩⟩
      · have htwo : Nat.card (M.openBoundaryPlaces U.ι) = 2 := by omega
        obtain ⟨x, y, hxy, hU⟩ := exists_complement_pair_of_boundary_card_two M U htwo
        obtain ⟨i⟩ := nonempty_laurent_iso_of_genus_zero_complement_pair M hg x y hxy U hU
        let E : FiniteEtale (Spec (.of (LaurentPolynomial K))) ≌ FiniteEtale U.toScheme :=
          MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤ i.symm
        have : (pullback i.hom).IsEquivalence := E.isEquivalence_functor
        obtain ⟨_g, eT, _hgen, _he⟩ :=
          exists_fundamentalGroup_laurent_profiniteInteger_equiv (xi ≫ i.hom)
        let e := (fundamentalGroupEquivOfPullbackEquivalence i.hom xi).trans eT
        exact ⟨⟨fun a b => e.injective
          ((e.map_mul a b).trans ((mul_comm (e a) (e b)).trans (e.map_mul b a).symm))⟩⟩
    · have : IsIso U.ι := isIso_of_openBoundary_card_eq_zero M U.ι hr
      let E : FiniteEtale M.C ≌ FiniteEtale U.toScheme :=
        MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤
          (asIso U.ι).symm
      have : (pullback U.ι).IsEquivalence := E.isEquivalence_functor
      let e := fundamentalGroupEquivOfPullbackEquivalence U.ι xi
      have : IsMulCommutative π₁ᵉᵗ(xi ≫ U.ι) :=
        isMulCommutative_fundamentalGroup_of_genus_one M hg (xi ≫ U.ι)
      exact ⟨⟨fun a b => e.injective
        ((e.map_mul a b).trans ((mul_comm (e a) (e b)).trans (e.map_mul b a).symm))⟩⟩

end AnabelianGeometry.GeometricFundamentalGroup
