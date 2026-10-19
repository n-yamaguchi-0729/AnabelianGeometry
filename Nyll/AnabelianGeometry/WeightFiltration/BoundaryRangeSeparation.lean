/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaCoordinateSeparation
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsProcyclic

/-! # Boundary places distinguished by their actual abelian inertia ranges -/

noncomputable section
open AlgebraicGeometry CategoryTheory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

variable
    {K F : Type} [Field K] [CharZero K] [IsAlgClosed K] [Field F] [Algebra K F]
    [IsCurveOver K F]
    (M : CurveModel K F)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    [Algebra F X.functionField]
    (hfield : algebraMap F X.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring F Ω]
    [Algebra K Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal] [hfin : Finite (M.openBoundaryPlaces j)]

include hfin hj hfield in
/-- With at least three punctures, the actual abelianized inertia ranges
still distinguish all boundary places. -/
theorem boundaryPlaceInertiaHom_range_injective
    (hthree : 3 ≤ Nat.card (M.openBoundaryPlaces j)) :
    Function.Injective (fun p : M.openBoundaryPlaces j =>
      (boundaryPlaceInertiaHom M j hj hfield Q p).toMonoidHom.range) := by
  classical
  intro p q hpq
  by_contra hne
  let := Fintype.ofFinite (M.openBoundaryPlaces j)
  have hthree' : 3 ≤ Fintype.card (M.openBoundaryPlaces j) := by
    simpa only [Nat.card_eq_fintype_card] using hthree
  have hlt : ({p, q} : Finset (M.openBoundaryPlaces j)).card <
      (Finset.univ : Finset (M.openBoundaryPlaces j)).card := by
    have hcard := Finset.card_le_two (a := p) (b := q)
    simp only [Finset.card_univ]
    omega
  obtain ⟨r, _, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hrpq : r ≠ p ∧ r ≠ q := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hr
  obtain ⟨t, ht⟩ := primeToRoots_exists_ne_one K K
  change (boundaryPlaceInertiaHom M j hj hfield Q p).toMonoidHom.range =
    (boundaryPlaceInertiaHom M j hj hfield Q q).toMonoidHom.range at hpq
  have hmem : boundaryPlaceInertiaHom M j hj hfield Q p t ∈
      (boundaryPlaceInertiaHom M j hj hfield Q q).toMonoidHom.range := by
    rw [← hpq]
    exact ⟨t, rfl⟩
  obtain ⟨u, hu⟩ := hmem
  exact ht (boundaryPlaceInertiaHom_eq_of_third M j hj hfield Q
    p q r hne hrpq.1.symm hrpq.2.symm t u hu.symm).1

end AnabelianGeometry.WeightFiltration
