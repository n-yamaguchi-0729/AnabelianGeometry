/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.CharacterCardinalityTorsionFree
import Nyll.JacobianVarieties.Kummer.OpenFiniteH1Cardinality
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenSubgroupFundamentalGroup
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverSquareBoundary
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverInvariants
import Nyll.AlgebraicCurves.Models.Points.RationalPointExistence
import Nyll.ProCGroups.FiniteStepSolvableQuotients.SlimnessAndTorsion

/-!
# Torsion-freeness of actual open-curve fundamental groups

The geometric formula for finite H1 has cardinality n^(2g+r-1).
The proved finite-character criterion makes the actual abelianization
torsion-free. Actual connected finite etale covers and their compactifications
supply this property for every actual open subgroup; the existing profinite
criterion then proves torsion-freeness of the full group.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open EtaleFundamentalGroups.Cohomology ProCGroups.FiniteStepSolvableQuotients

namespace AnabelianGeometry

/-- The abelianization is torsion-free by actual finite H1 cardinalities
and their actual character comparison, including the boundary contribution. -/
theorem isMulTorsionFree_abelianization_fundamentalGroup_open_curve
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j]
    (hb : (M.openBoundaryPlaces j).Nonempty)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (geom : Spec (.of Ω) ⟶ X) :
    IsMulTorsionFree (TopologicalAbelianization (Aut (FiniteEtale.fiber geom))) := by
  classical
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  let : Fintype (M.openBoundaryPlaces j) := (M.openBoundaryPlaces_finite j).fintype
  obtain ⟨v₀, hv₀⟩ := hb
  have hj : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  have : TotallyDisconnectedSpace
      (TopologicalAbelianization (Aut (FiniteEtale.fiber geom))) :=
    _root_.ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator (Aut (FiniteEtale.fiber geom)))
      (Subgroup.isClosed_closedCommutator _)
  apply ProCGroups.isMulTorsionFree_of_rootsOfUnity_character_card K
    (2 * genusFF K F + Fintype.card (M.openBoundaryPlaces j) - 1)
  intro n htop hdiscrete
  have ht : htop = ⊥ := hdiscrete.eq_bot
  subst htop
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let A : AddCommGrpCat := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  calc
    Nat.card (TopologicalAbelianization (Aut (FiniteEtale.fiber geom)) →ₜ*
        rootsOfUnity (n : ℕ) K) =
        Nat.card (Sheaf.H.{0}
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj A) 1) :=
      (Nat.card_congr ((finiteH1AbelianCharacterEquiv A geom).toEquiv.trans
        Additive.toMul)).symm
    _ = (n : ℕ) ^ (2 * genusFF K F + Fintype.card (M.openBoundaryPlaces j) - 1) :=
      M.natCard_open_finiteH1_eq_pow_genus_boundary ε j hj ⟨v₀, hv₀⟩ n geom

/-- Every actual open subgroup of the open curve's fundamental group has
torsion-free abelianization; its covering curve is constructed geometrically. -/
theorem isAbTorsionFree_fundamentalGroup_open_curve
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F) {X : Scheme}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (hb : (M.openBoundaryPlaces j).Nonempty)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (geom : Spec (.of Ω) ⟶ X) :
    IsAbTorsionFree (Aut (FiniteEtale.fiber geom)) := by
  intro H
  have : IsTopologicalGroup H := by
    change IsTopologicalGroup ↥(H : Subgroup (Aut (FiniteEtale.fiber geom)))
    infer_instance
  obtain ⟨A, hA, geomA, _, eA, _⟩ :=
    FiniteEtale.exists_connectedCover_lift_fundamentalGroup_equiv_openSubgroup geom H
  have : IsConnected A := FiniteEtale.isConnected_of_connectedSpace_left A
  have : IsIntegral A.left := isIntegral_left_of_isConnected_finiteEtale A
  have : IsIntegral ((Functor.id Scheme).obj A.left) :=
    inferInstanceAs (IsIntegral A.left)
  have : IsIntegral ((Functor.fromPUnit X).obj A.right) :=
    inferInstanceAs (IsIntegral X)
  have : IsFiniteEtale A.hom := A.prop
  have : CompactSpace A.left :=
    QuasiCompact.compactSpace_of_compactSpace (X := A.left) (Y := X) A.hom
  have : Surjective A.hom := IsFiniteEtale.surjective A.hom
  let cA : A.left ⟶ Spec (.of K) := A.hom ≫ j ≫ M.toBase
  let : Algebra K A.left.functionField := (baseToFunctionField cA).toAlgebra
  obtain ⟨N, d, k, hd, hfinite, hk, hsquare, hboundary⟩ :=
    exists_open_cover_curveModel_square_boundary M j A
  have : IsFinite d := hfinite
  have : IsOpenImmersion k := hk
  have hsurj : Function.Surjective d :=
    surjective_finite_extension_of_open_square j A.hom A.hom.surjective k d hsquare
  have hNboundary :=
    openBoundary_nonempty_of_finite_square M N d hd hsurj j k hboundary hb
  have : IsMulTorsionFree
      (TopologicalAbelianization (Aut (FiniteEtale.fiber geomA))) :=
    isMulTorsionFree_abelianization_fundamentalGroup_open_curve N k hNboundary geomA
  exact (ProCGroups.Abelian.TopologicalAbelianization.congr eA).isMulTorsionFree

/-- The actual fundamental group of a smooth open curve over an algebraically
closed characteristic-zero field has no nontrivial finite-order element. -/
theorem isTorsionFreeGroup_fundamentalGroup_open_curve
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F) {X : Scheme}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (hb : (M.openBoundaryPlaces j).Nonempty)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (geom : Spec (.of Ω) ⟶ X) :
    IsTorsionFreeGroup (Aut (FiniteEtale.fiber geom)) :=
  isTorsionFreeGroup_of_isAbTorsionFree
    (isAbTorsionFree_fundamentalGroup_open_curve M j hb geom)

end AnabelianGeometry
