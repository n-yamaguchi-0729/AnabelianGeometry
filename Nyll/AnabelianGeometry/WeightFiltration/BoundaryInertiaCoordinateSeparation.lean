/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaRelations

/-!
# Separation of actual boundary inertia coordinates

Two boundary points suffice for injectivity of each roots coordinate.
Three suffice to separate the images of distinct coordinates. These
statements concern the actual boundary maps, not an auxiliary module.
-/

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
    [hfin : Finite (M.openBoundaryPlaces j)]

omit hfin [IsCurveOver K F] [CompactSpace X] [Algebra K Ω]
  [∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω] in
/-- The actual product map on a single coordinate. -/
theorem boundaryInertiaMap_mulSingle
    [Fintype (M.openBoundaryPlaces j)]
    [DecidableEq (M.openBoundaryPlaces j)]
    (p : M.openBoundaryPlaces j)
    (t : (primeToRootsSystem K K).inverseLimit) :
    boundaryInertiaMap M j hj hfield Q (Pi.mulSingle p t) =
      boundaryPlaceInertiaHom M j hj hfield Q p t := by
  classical
  change MonoidHom.noncommPiCoprod
    (fun p => (boundaryPlaceInertiaHom M j hj hfield Q p).toMonoidHom)
    (fun _ _ _ _ _ => Commute.all _ _) (Pi.mulSingle p t) = _
  exact MonoidHom.noncommPiCoprod_mulSingle
    (fun p => (boundaryPlaceInertiaHom M j hj hfield Q p).toMonoidHom) p t

include hfin in
/-- A second boundary point makes this actual coordinate injective. -/
theorem boundaryPlaceInertiaHom_injective_of_ne
    (p q : M.openBoundaryPlaces j) (hpq : p ≠ q) :
    Function.Injective (boundaryPlaceInertiaHom M j hj hfield Q p) := by
  classical
  intro x y hxy
  let := Fintype.ofFinite (M.openBoundaryPlaces j)
  have ht :
      boundaryInertiaMap M j hj hfield Q
        (Pi.mulSingle p (x / y)) = 1 := by
    rw [boundaryInertiaMap_mulSingle M j hj hfield Q, map_div]
    exact div_eq_one.mpr hxy
  have hc :=
    (boundaryInertiaMap_eq_one_iff M j hj hfield Q _).mp ht p q
  have hdiv : x / y = 1 := by
    simpa [hpq, hpq.symm] using hc
  exact div_eq_one.mp hdiv

include hfin in
/-- Every coordinate is injective when there are at least two places. -/
theorem boundaryPlaceInertiaHom_injective
    [Nontrivial (M.openBoundaryPlaces j)]
    (p : M.openBoundaryPlaces j) :
    Function.Injective (boundaryPlaceInertiaHom M j hj hfield Q p) := by
  obtain ⟨q, hqp⟩ := exists_ne p
  exact boundaryPlaceInertiaHom_injective_of_ne
    M j hj hfield Q p q hqp.symm

include hfin in
/-- Distinct actual coordinates meet only at one if a third place exists. -/
theorem boundaryPlaceInertiaHom_eq_of_third
    (p q r : M.openBoundaryPlaces j)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (x y : (primeToRootsSystem K K).inverseLimit)
    (hxy :
      boundaryPlaceInertiaHom M j hj hfield Q p x =
        boundaryPlaceInertiaHom M j hj hfield Q q y) :
    x = 1 ∧ y = 1 := by
  classical
  let := Fintype.ofFinite (M.openBoundaryPlaces j)
  let t : M.openBoundaryPlaces j →
      (primeToRootsSystem K K).inverseLimit :=
    Pi.mulSingle p x / Pi.mulSingle q y
  have ht : boundaryInertiaMap M j hj hfield Q t = 1 := by
    dsimp [t]
    rw [map_div, boundaryInertiaMap_mulSingle M j hj hfield Q,
      boundaryInertiaMap_mulSingle M j hj hfield Q]
    exact div_eq_one.mpr hxy
  have hc :=
    (boundaryInertiaMap_eq_one_iff M j hj hfield Q t).mp ht
  constructor
  · simpa [t, hpq, hpq.symm, hpr, hpr.symm, hqr, hqr.symm]
      using hc p r
  · simpa [t, hpq, hpq.symm, hpr, hpr.symm, hqr, hqr.symm]
      using hc q r

include hfin in
/-- The two actual coordinate ranges have trivial intersection. -/
theorem boundaryPlaceInertiaHom_range_inf_eq_bot
    (p q r : M.openBoundaryPlaces j)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (boundaryPlaceInertiaHom M j hj hfield Q p).toMonoidHom.range ⊓
      (boundaryPlaceInertiaHom M j hj hfield Q q).toMonoidHom.range = ⊥ := by
  apply le_antisymm
  · intro z hz
    obtain ⟨x, hx⟩ := hz.1
    obtain ⟨y, hy⟩ := hz.2
    have hxy := boundaryPlaceInertiaHom_eq_of_third
      M j hj hfield Q p q r hpq hpr hqr x y (hx.trans hy.symm)
    have hz1 : z = 1 := by
      rw [← hx, hxy.1, map_one]
    exact hz1
  · exact bot_le

end AnabelianGeometry.WeightFiltration
