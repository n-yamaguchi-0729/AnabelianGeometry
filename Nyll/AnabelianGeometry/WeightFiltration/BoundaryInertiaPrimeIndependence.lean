/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaRelations

/-!
# Independence of normalization primes in abelian boundary inertia

The finite residue formula identifies the maps for any two prime families.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia EtaleFundamentalGroups.Cohomology
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

variable
    {K F : Type} [Field K] [CharZero K] [IsAlgClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    [Algebra F X.functionField]
    (hfield : algebraMap F X.functionField = (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring F Ω]
    [Algebra K Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal]
    (Q' : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q' p).IsMaximal]


/-- The abelianized boundary parameter is independent of the normalization primes. -/
theorem boundaryPlaceInertiaHom_independent_of_primes
    (p : M.openBoundaryPlaces j) (t : (primeToRootsSystem K K).inverseLimit) :
    boundaryPlaceInertiaHom M j hj hfield Q p t =
      boundaryPlaceInertiaHom M j hj hfield Q' p t := by
  classical
  let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
  let ξ := η ≫ X.fromSpecStalk (genericPoint X)
  let G := Aut (FiniteEtale.fiber ξ)
  let P := TopologicalAbelianization G
  let : TotallyDisconnectedSpace P :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator G) (Subgroup.isClosed_closedCommutator G)
  have hchars (n : ℕ+) :
      let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
      ∀ χ : P →ₜ* rootsOfUnity (n : ℕ) K,
        χ (boundaryPlaceInertiaHom M j hj hfield Q p t) =
          χ (boundaryPlaceInertiaHom M j hj hfield Q' p t) := by
    intro topology χ
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    have hn : IsUnit ((n : ℕ) : K) :=
      isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
    let B := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let : TopologicalSpace (Multiplicative B) := ⊥
    let : DiscreteTopology (Multiplicative B) := ⟨rfl⟩
    obtain ⟨x, hχ⟩ :=
      (finiteH1AbelianCharacterEquiv B ξ).toEquiv.surjective (Additive.ofMul χ)
    change h1AbelianCharacter B ξ x = χ at hχ
    rw [← hχ]
    exact (boundaryPlaceInertiaHom_h1Value M j hj hfield Q n hn p x t).trans
      (boundaryPlaceInertiaHom_h1Value M j hj hfield Q' n hn p x t).symm
  let H : ClosedSubgroup P := ⟨⊥, by
    change IsClosed ({1} : Set P)
    exact isClosed_singleton⟩
  apply div_eq_one.mp
  exact mem_closedSubgroup_of_rootCharacters K H
    (boundaryPlaceInertiaHom M j hj hfield Q p t /
      boundaryPlaceInertiaHom M j hj hfield Q' p t) (by
        intro n topology χ _
        rw [map_div, hchars n χ, div_self'])

end AnabelianGeometry.WeightFiltration
