/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.CurveH1Cardinality
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.SmallBoundaryCharts
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.GenusZeroFundamentalGroup
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
import Mathlib.Data.Nat.Log

/-! # Trivial geometric fundamental groups are exactly the (0,0) and (0,1) cases -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace NeronModelInfra
open AlgebraicGeometry.FiniteEtale EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.GeometricFundamentalGroup

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The full geometric fundamental group of a smooth curve is trivial
exactly when its proper genus is zero and at most one point is omitted.
The only data are the actual compactification, its open, and the base point. -/
theorem subsingleton_fundamentalGroup_iff_genus_zero_boundary_le_one
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F) (U : M.C.Opens)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ U.toScheme) :
    Subsingleton π₁ᵉᵗ(xi) ↔
      genusFF K F = 0 ∧ Nat.card (M.openBoundaryPlaces U.ι) ≤ 1 := by
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
  · intro hπ
    let C := AddCommGrpCat.of (Additive (rootsOfUnity 2 K))
    let H := Sheaf.H.{0}
      ((constantSheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{0}).obj C) 1
    let : TopologicalSpace (Multiplicative C) := ⊥
    have : DiscreteTopology (Multiplicative C) := ⟨rfl⟩
    let e := finiteH1CharacterEquiv C xi
    have hchar : Subsingleton (Additive (π₁ᵉᵗ(xi) →ₜ* Multiplicative C)) := by
      refine ⟨fun a b => ?_⟩
      apply ContinuousMonoidHom.ext
      intro g
      change a.toMul g = b.toMul g
      rw [hπ.elim g 1, map_one, map_one]
    have : Subsingleton H := ⟨fun a b => e.injective (hchar.elim (e a) (e b))⟩
    have hH : Nat.card H = 1 := Nat.card_unique
    have hcard := natCard_finiteH1_eq_pow_genus_boundary M U.ι ⟨2, by decide⟩ xi
    have hpow : 2 ^ (2 * genusFF K F + (Nat.card (M.openBoundaryPlaces U.ι) - 1)) = 1 :=
      hcard.symm.trans hH
    have hlog := congrArg (Nat.log 2) hpow
    rw [Nat.log_pow (by decide : 1 < 2), Nat.log_one_right] at hlog
    omega
  · rintro ⟨hg, hr⟩
    by_cases hzero : Nat.card (M.openBoundaryPlaces U.ι) = 0
    · have : IsIso U.ι := isIso_of_openBoundary_card_eq_zero M U.ι hzero
      let E : FiniteEtale M.C ≌ FiniteEtale U.toScheme :=
        MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤
          (asIso U.ι).symm
      have : (pullback U.ι).IsEquivalence := E.isEquivalence_functor
      let e := fundamentalGroupEquivOfPullbackEquivalence U.ι xi
      have hproper := subsingleton_fundamentalGroup_of_genus_zero M hg (xi ≫ U.ι)
      exact ⟨fun a b => e.injective (hproper.elim (e a) (e b))⟩
    · have hone : Nat.card (M.openBoundaryPlaces U.ι) = 1 := by omega
      obtain ⟨x, hx⟩ := exists_complement_singleton_of_boundary_card_one M U hone
      exact subsingleton_fundamentalGroup_of_genus_zero_complement M hg x U hx xi

end AnabelianGeometry.GeometricFundamentalGroup
