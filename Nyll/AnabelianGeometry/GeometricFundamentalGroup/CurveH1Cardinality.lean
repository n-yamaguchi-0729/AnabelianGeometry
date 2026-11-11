/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Charts.NotIsAffineProper
public import Nyll.AnabelianGeometry.GeometricFundamentalGroup.OpenCoverH1Numerics
public import Nyll.AnabelianGeometry.GeometricFundamentalGroup.CoverCohomologyTransport
public import Nyll.JacobianVarieties.Kummer.FiniteH1Cardinality
public import Nyll.JacobianVarieties.Kummer.OpenFiniteH1Cardinality
public import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
public import Nyll.SchemeTheory.Pi1.Affine.Over
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # One H¹ cardinality formula for proper and punctured curves -/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace NeronModelInfra
open AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.GeometricFundamentalGroup

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The finite H¹ exponent is 2g + (r - 1), with natural subtraction.
For r = 0 this is the proper formula 2g; for r > 0 it is 2g + r - 1.
The compactification point and the proper/open comparison are constructed. -/
theorem natCard_finiteH1_eq_pow_genus_boundary_of_isUnit
    {K : Type uGeom} {F : Type uField₁} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] (M : CurveModel K F)
    {X : Scheme.{uGeom}} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    {Ω : Type uGeom} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    Nat.card (Sheaf.H.{uGeom}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{uGeom}).obj
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
      MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme.{uGeom}) ⊤
        (asIso j).symm
    have : (pullback j).IsEquivalence := E.isEquivalence_functor
    let e := fundamentalGroupEquivOfPullbackEquivalence j xi
    have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
    let C := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    have h := (Nat.card_congr
      (finiteH1EquivOfFundamentalGroupEquiv xi (xi ≫ j) e C).toEquiv).trans
        (M.natCard_finiteH1_eq_pow_genus_of_isUnit ε n hn (xi ≫ j))
    simpa only [hr, Nat.zero_sub, Nat.add_zero] using h
  · have hpos : 0 < Fintype.card (M.openBoundaryPlaces j) := by
      rw [← Nat.card_eq_fintype_card]
      omega
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpos
    have hdense : DenseRange j :=
      j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
    have h := M.natCard_open_finiteH1_eq_pow_genus_boundary_of_isUnit ε j hdense v n hn xi
    have hexp : 2 * genusFF K F + Fintype.card (M.openBoundaryPlaces j) - 1 =
        2 * genusFF K F + (Nat.card (M.openBoundaryPlaces j) - 1) := by
      rw [Nat.card_eq_fintype_card]
      omega
    exact h.trans (congrArg ((n : ℕ) ^ ·) hexp)

/-- The finite H¹ exponent is 2g + (r - 1), with natural subtraction.
For r = 0 this is the proper formula 2g; for r > 0 it is 2g + r - 1.
The compactification point and the proper/open comparison are constructed. -/
theorem natCard_finiteH1_eq_pow_genus_boundary
    {K : Type uGeom} {F : Type uField₁} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F)
    {X : Scheme.{uGeom}} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (n : ℕ+)
    {Ω : Type uGeom} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    Nat.card (Sheaf.H.{uGeom}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{uGeom}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1) =
      (n : ℕ) ^ (2 * genusFF K F + (Nat.card (M.openBoundaryPlaces j) - 1)) :=
  natCard_finiteH1_eq_pow_genus_boundary_of_isUnit M j n
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)) xi

/-- A nonempty affine open of a smooth proper curve has a nonempty boundary. -/
theorem openBoundary_card_pos_of_isAffine
    {K : Type uGeom} {F : Type uField₁} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme.{uGeom}} [Nonempty X] [IsAffine X]
    (j : X ⟶ M.C) [IsOpenImmersion j] : 0 < Nat.card (M.openBoundaryPlaces j) := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have : IsIso j := isIso_of_openBoundary_card_eq_zero M j hzero
  have hA : IsAffine M.C := IsAffine.of_isIso (inv j)
  apply AlgebraicCurve.not_isAffine_of_isProper_of_isCurveOver K M.toBase ?_ hA
  let : Algebra K M.C.functionField := (baseToFunctionField M.toBase).toAlgebra
  exact isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
    (RingEquiv.refl _) (fun _ => rfl)

/-- An isomorphism of the actual geometric abelianizations preserves the
finite-coefficient H¹ exponent, in every characteristic where n is invertible. -/
theorem genus_boundary_exponent_eq_of_abelianization_equiv
    {K : Type uGeom} {F : Type uField₁} {G : Type uField₂} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] [Field G] [Algebra K G]
    (M : CurveModel K F) (N : CurveModel K G)
    {X Y : Scheme.{uGeom}} [IsIntegral X] [CompactSpace X] [IsIntegral Y] [CompactSpace Y]
    (i : X ⟶ M.C) (j : Y ⟶ N.C) [IsOpenImmersion i] [IsOpenImmersion j]
    {Ω₁ Ω₂ : Type uGeom} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (x : Spec (.of Ω₁) ⟶ X) (y : Spec (.of Ω₂) ⟶ Y)
    (e : TopologicalAbelianization (π₁ᵉᵗ(x)) ≃ₜ*
      TopologicalAbelianization (π₁ᵉᵗ(y)))
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) (hn₂ : 2 ≤ (n : ℕ)) :
    2 * genusFF K F + (Nat.card (M.openBoundaryPlaces i) - 1) =
      2 * genusFF K G + (Nat.card (N.openBoundaryPlaces j) - 1) := by
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let C := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let E := finiteH1EquivOfAbelianizationEquiv x y e C
  have h := Nat.card_congr E.toEquiv
  rw [natCard_finiteH1_eq_pow_genus_boundary_of_isUnit M i n hn x,
    natCard_finiteH1_eq_pow_genus_boundary_of_isUnit N j n hn y] at h
  exact Nat.pow_right_injective hn₂ h

/-- Hyperbolicity of affine curves is invariant under an isomorphism of their
actual geometric abelianizations. Only one invertible exponent above one is used. -/
theorem hyperbolic_iff_of_affine_abelianization_equiv
    {K : Type uGeom} {F : Type uField₁} {G : Type uField₂} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] [Field G] [Algebra K G]
    (M : CurveModel K F) (N : CurveModel K G)
    {X Y : Scheme.{uGeom}} [IsIntegral X] [IsAffine X] [IsIntegral Y] [IsAffine Y]
    (i : X ⟶ M.C) (j : Y ⟶ N.C) [IsOpenImmersion i] [IsOpenImmersion j]
    {Ω₁ Ω₂ : Type uGeom} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (x : Spec (.of Ω₁) ⟶ X) (y : Spec (.of Ω₂) ⟶ Y)
    (e : TopologicalAbelianization (π₁ᵉᵗ(x)) ≃ₜ*
      TopologicalAbelianization (π₁ᵉᵗ(y)))
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) (hn₂ : 2 ≤ (n : ℕ)) :
    (0 < 2 * (genusFF K F : ℤ) - 2 + (Nat.card (M.openBoundaryPlaces i) : ℤ)) ↔
      0 < 2 * (genusFF K G : ℤ) - 2 + (Nat.card (N.openBoundaryPlaces j) : ℤ) := by
  have h := genus_boundary_exponent_eq_of_abelianization_equiv M N i j x y e n hn hn₂
  have hi := openBoundary_card_pos_of_isAffine M i
  have hj := openBoundary_card_pos_of_isAffine N j
  omega

end AnabelianGeometry.GeometricFundamentalGroup
