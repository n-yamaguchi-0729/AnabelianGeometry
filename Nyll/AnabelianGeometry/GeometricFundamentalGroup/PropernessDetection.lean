/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.OpenCoverH1Numerics
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.ProperCoverH1Degree
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.PositiveGenusCover
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.CoverCohomologyTransport
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Nyll.SchemeTheory.Pi1.Affine.Over

/-! # Detecting properness from the full geometric fundamental group

A positive-genus proper curve and a punctured curve cannot have isomorphic
geometric fundamental groups. A degree-two cover exists on the proper side;
its actual transport has the same degree and finite H¹. Riemann--Hurwitz
then contradicts the different proper and open H¹ formulas. This is the
full-group cover-detection argument; it makes no finite-derived-quotient claim.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace NeronModelInfra
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open AlgebraicGeometry.FiniteEtale
open EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.GeometricFundamentalGroup

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- Positive-genus proper curves and nonproper curves have nonisomorphic
full geometric fundamental groups. Their genera need not be assumed equal. -/
theorem not_nonempty_fundamentalGroupEquiv_proper_open
    {K F E : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [Field E] [Algebra K E]
    (M : CurveModel K F) (N : CurveModel K E) (hg : 0 < genusFF K F)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ N.C) [IsOpenImmersion j]
    (hboundary : (N.openBoundaryPlaces j).Nonempty)
    {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (x : Spec (.of Ω₁) ⟶ M.C) (y : Spec (.of Ω₂) ⟶ X) :
    ¬ Nonempty (π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(y)) := by
  classical
  rintro ⟨e⟩
  have : Smooth N.toBase := SmoothOfRelativeDimension.smooth 1 N.toBase
  have : Smooth (j ≫ N.toBase) := inferInstance
  have : IsLocallyNoetherian N.C := LocallyOfFiniteType.isLocallyNoetherian N.toBase
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion j
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral X := IsNormalIntegral.of_stalks X
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk (j ≫ N.toBase) z).2)
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  have : IsCurveOver K E :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one N.toBase
      N.ffEquiv N.ffEquiv_algebraMap
  have : GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase
  obtain ⟨εM⟩ := M.nonempty_rationalPoint
  obtain ⟨εN⟩ := N.nonempty_rationalPoint
  let : Fintype (N.openBoundaryPlaces j) := (N.openBoundaryPlaces_finite j).fintype
  obtain ⟨v, hv⟩ := hboundary
  have hrpos : 0 < Fintype.card (N.openBoundaryPlaces j) :=
    Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
  let n : ℕ+ := ⟨2, by decide⟩
  have : NeZero ((n : ℕ) : K) := ⟨Nat.cast_ne_zero.mpr n.ne_zero⟩
  let C := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  have hj : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  have hbase := Nat.card_congr (finiteH1EquivOfFundamentalGroupEquiv x y e C).toEquiv
  dsimp only [C] at hbase
  rw [M.natCard_finiteH1_eq_pow_genus εM n x,
    N.natCard_open_finiteH1_eq_pow_genus_boundary εN j hj ⟨v, hv⟩ n y] at hbase
  have hbaseLog := congrArg (Nat.log 2) hbase
  change Nat.log 2 (2 ^ (2 * genusFF K F)) =
    Nat.log 2 (2 ^ (2 * genusFF K E + Fintype.card (N.openBoundaryPlaces j) - 1))
      at hbaseLog
  rw [Nat.log_pow (by decide : 1 < 2), Nat.log_pow (by decide : 1 < 2)] at hbaseLog
  obtain ⟨A, hA, a, ha, hdegreeA⟩ :=
    exists_primeDegree_finiteEtale_cover_of_genus_pos M hg x 2 Nat.prime_two
  have : IsGalois A := hA
  have : ConnectedSpace A.left := connectedSpace_left_of_isConnected A
  obtain ⟨B, hB, b, hb, _eB, hGal, _hsquare, hdegree, hH1⟩ :=
    exists_connected_cover_preserving_degree_and_h1 x y e A a ha
  have : ConnectedSpace B.left := hB
  have : IsGalois B := hGal hA
  obtain ⟨qP, hPcard, hP⟩ := exists_finiteH1_exponent_proper_cover M A x a n
  obtain ⟨qO, hOcard, hO⟩ :=
    exists_openCover_finiteH1_exponent N j ⟨v, hv⟩ B n y b hb
  have hcard := hH1 C inferInstance
  dsimp only [C] at hcard
  rw [hPcard, hOcard] at hcard
  have hq := congrArg (Nat.log 2) hcard
  change Nat.log 2 (2 ^ qP) = Nat.log 2 (2 ^ qO) at hq
  rw [Nat.log_pow (by decide : 1 < 2), Nat.log_pow (by decide : 1 < 2)] at hq
  rw [hdegreeA] at hP
  rw [hdegree, hdegreeA, Nat.card_eq_fintype_card] at hO
  have hbZ : 2 * (genusFF K F : ℤ) =
      2 * (genusFF K E : ℤ) + Fintype.card (N.openBoundaryPlaces j) - 1 := by omega
  omega

/-- For two positive-genus smooth curves, an isomorphism of their full
geometric fundamental groups preserves whether their actual boundaries
are empty. No arithmetic action or boundary subgroup is supplied. -/
theorem openBoundary_card_eq_zero_iff_of_positive_genus
    {K F E : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [Field E] [Algebra K E]
    (M : CurveModel K F) (N : CurveModel K E)
    (hgM : 0 < genusFF K F) (hgN : 0 < genusFF K E)
    {X Y : Scheme} [IsIntegral X] [CompactSpace X] [IsIntegral Y] [CompactSpace Y]
    (j : X ⟶ M.C) (k : Y ⟶ N.C) [IsOpenImmersion j] [IsOpenImmersion k]
    {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (x : Spec (.of Ω₁) ⟶ X) (y : Spec (.of Ω₂) ⟶ Y)
    (e : π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(y)) :
    Nat.card (M.openBoundaryPlaces j) = 0 ↔ Nat.card (N.openBoundaryPlaces k) = 0 := by
  classical
  let : Fintype (M.openBoundaryPlaces j) := (M.openBoundaryPlaces_finite j).fintype
  let : Fintype (N.openBoundaryPlaces k) := (N.openBoundaryPlaces_finite k).fintype
  constructor
  · intro hM
    by_contra hN
    have hNpos : 0 < Fintype.card (N.openBoundaryPlaces k) := by
      rw [← Nat.card_eq_fintype_card]
      omega
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hNpos
    have : IsIso j := isIso_of_openBoundary_card_eq_zero M j hM
    let T : FiniteEtale M.C ≌ FiniteEtale X :=
      MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤ (asIso j).symm
    have : (pullback j).IsEquivalence := T.isEquivalence_functor
    let E := (fundamentalGroupEquivOfPullbackEquivalence j x).symm.trans e
    exact not_nonempty_fundamentalGroupEquiv_proper_open M N hgM k
      ⟨v.val, v.property⟩ (x ≫ j) y ⟨E⟩
  · intro hN
    by_contra hM
    have hMpos : 0 < Fintype.card (M.openBoundaryPlaces j) := by
      rw [← Nat.card_eq_fintype_card]
      omega
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hMpos
    have : IsIso k := isIso_of_openBoundary_card_eq_zero N k hN
    let T : FiniteEtale N.C ≌ FiniteEtale Y :=
      MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤ (asIso k).symm
    have : (pullback k).IsEquivalence := T.isEquivalence_functor
    let E := (fundamentalGroupEquivOfPullbackEquivalence k y).symm.trans e.symm
    exact not_nonempty_fundamentalGroupEquiv_proper_open N M hgN j
      ⟨v.val, v.property⟩ (y ≫ k) x ⟨E⟩

end AnabelianGeometry.GeometricFundamentalGroup
