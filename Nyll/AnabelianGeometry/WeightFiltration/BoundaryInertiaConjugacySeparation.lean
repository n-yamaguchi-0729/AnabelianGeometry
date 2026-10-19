/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaProcyclic

/-! # Actual boundary places are distinguished by their inertia conjugacy classes

Abelianization removes the conjugating element. The already proved separation
of the actual roots coordinates then distinguishes two places whenever a third
boundary place exists. No correspondence of boundary indices is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

private theorem commutativeHom_eq_of_conjugate_eq
    {G A : Type*} [Group G] [CommGroup A] (f : G →* A) (a x y : G)
    (h : (MulAut.conj a) x = y) : f y = f x := by
  have hmap : f ((MulAut.conj a) x) = f x := by
    change f (a * x * a⁻¹) = f x
    rw [map_mul, map_mul, map_inv, mul_comm (f a) (f x),
      mul_assoc, mul_inv_cancel, mul_one]
  exact (congrArg f h).symm.trans hmap

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
/-- Distinct actual boundary places have distinct inertia conjugacy classes. -/
theorem boundaryPlace_eq_of_inertia_eq_conjugate
    (hthree : 3 ≤ Nat.card (M.openBoundaryPlaces j))
    (p q : M.openBoundaryPlaces j)
    (a : Aut (FiniteEtale.fiber
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X))))
    (h : genericPlaceInertia X p.val (Q p) =
      (genericPlaceInertia X q.val (Q q)).map (MulAut.conj a).toMonoidHom) :
    p = q := by
  classical
  by_contra hpq
  let := Fintype.ofFinite (M.openBoundaryPlaces j)
  have hthree' : 3 ≤ Fintype.card (M.openBoundaryPlaces j) := by
    simpa only [Nat.card_eq_fintype_card] using hthree
  have hlt : ({p, q} : Finset (M.openBoundaryPlaces j)).card <
      (Finset.univ : Finset (M.openBoundaryPlaces j)).card := by
    have hp := Finset.card_le_two (a := p) (b := q)
    simp only [Finset.card_univ]
    omega
  obtain ⟨r, _, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hrpq : r ≠ p ∧ r ≠ q := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hr
  obtain ⟨t, ht⟩ := primeToRoots_exists_ne_one K K
  have hmem : boundaryPlaceInertiaLift M j hj hfield Q p t ∈
      genericPlaceInertia X p.val (Q p) := by
    rw [← boundaryPlaceInertiaLift_range M j hj hfield Q p]
    exact ⟨t, rfl⟩
  rw [h] at hmem
  obtain ⟨x, hx, hxt⟩ := hmem
  rw [← boundaryPlaceInertiaLift_range M j hj hfield Q q] at hx
  obtain ⟨u, rfl⟩ := hx
  have hcoordinate : boundaryPlaceInertiaHom M j hj hfield Q p t =
      boundaryPlaceInertiaHom M j hj hfield Q q u := by
    change TopologicalAbelianization.mk _ (boundaryPlaceInertiaLift M j hj hfield Q p t) =
      TopologicalAbelianization.mk _ (boundaryPlaceInertiaLift M j hj hfield Q q u)
    exact commutativeHom_eq_of_conjugate_eq
      (TopologicalAbelianization.mk _) a _ _ hxt
  exact ht (boundaryPlaceInertiaHom_eq_of_third M j hj hfield Q
    p q r hpq hrpq.1.symm hrpq.2.symm t u hcoordinate).1

end AnabelianGeometry.WeightFiltration
