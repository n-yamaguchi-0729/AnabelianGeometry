/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.OpenCoverH1Numerics
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.CoverCohomologyTransport
import Nyll.JacobianVarieties.Kummer.FiniteH1Cardinality
import Nyll.JacobianVarieties.Kummer.OpenFiniteH1Cardinality
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Nyll.SchemeTheory.Pi1.Affine.Over
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # One H¹ cardinality formula for proper and punctured curves -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace NeronModelInfra
open AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.GeometricFundamentalGroup

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The finite H¹ exponent is 2g + (r - 1), with natural subtraction.
For r = 0 this is the proper formula 2g; for r > 0 it is 2g + r - 1.
The compactification point and the proper/open comparison are constructed. -/
theorem natCard_finiteH1_eq_pow_genus_boundary
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (n : ℕ+)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    Nat.card (Sheaf.H.{0}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1) =
      (n : ℕ) ^ (2 * genusFF K F + (Nat.card (M.openBoundaryPlaces j) - 1)) := by
  classical
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  have : GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  let : Fintype (M.openBoundaryPlaces j) := (M.openBoundaryPlaces_finite j).fintype
  by_cases hr : Nat.card (M.openBoundaryPlaces j) = 0
  · have : IsIso j := isIso_of_openBoundary_card_eq_zero M j hr
    let E : FiniteEtale M.C ≌ FiniteEtale X :=
      MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤
        (asIso j).symm
    have : (pullback j).IsEquivalence := E.isEquivalence_functor
    let e := fundamentalGroupEquivOfPullbackEquivalence j xi
    have : NeZero ((n : ℕ) : K) := ⟨Nat.cast_ne_zero.mpr n.ne_zero⟩
    let C := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    have h := (Nat.card_congr
      (finiteH1EquivOfFundamentalGroupEquiv xi (xi ≫ j) e C).toEquiv).trans
        (M.natCard_finiteH1_eq_pow_genus ε n (xi ≫ j))
    simpa only [hr, Nat.zero_sub, Nat.add_zero] using h
  · have hpos : 0 < Fintype.card (M.openBoundaryPlaces j) := by
      rw [← Nat.card_eq_fintype_card]
      omega
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpos
    have hdense : DenseRange j :=
      j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
    have h := M.natCard_open_finiteH1_eq_pow_genus_boundary ε j hdense v n xi
    have hexp : 2 * genusFF K F + Fintype.card (M.openBoundaryPlaces j) - 1 =
        2 * genusFF K F + (Nat.card (M.openBoundaryPlaces j) - 1) := by
      rw [Nat.card_eq_fintype_card]
      omega
    exact h.trans (congrArg ((n : ℕ) ^ ·) hexp)

end AnabelianGeometry.GeometricFundamentalGroup
