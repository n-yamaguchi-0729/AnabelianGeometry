/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaCoordinateSeparation
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsTorsionFree

/-!
# Embedded actual boundary inertia

The actual roots parameter injects into the original fundamental group and
remains injective after abelianization when a second boundary point exists.
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

/-- The actual boundary inertia map before abelianization. -/
def boundaryPlaceInertiaLift (p : M.openBoundaryPlaces j) :
    (primeToRootsSystem K K).inverseLimit →ₜ*
      Aut (FiniteEtale.fiber (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X))) := by
  have hsurj : Function.Surjective (algebraMap F X.functionField) := by
    rw [hfield]
    exact (j.functionFieldRingEquivOfIsOpenImmersion).surjective.comp M.ffEquiv.surjective
  exact (genericPlaceInertiaHom X p.val (Q p) hsurj).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (placeInertiaConstantRootsEquiv K F Ω p.val (Q p)))

omit hfin [IsCurveOver K F] [CompactSpace X] [Algebra K Ω]
  [∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω] in
/-- The lifted roots parameter has exactly the original global inertia image. -/
theorem boundaryPlaceInertiaLift_range (p : M.openBoundaryPlaces j) :
    (boundaryPlaceInertiaLift M j hj hfield Q p).toMonoidHom.range =
      genericPlaceInertia X p.val (Q p) := by
  have hsurj : Function.Surjective (algebraMap F X.functionField) := by
    rw [hfield]
    exact (j.functionFieldRingEquivOfIsOpenImmersion).surjective.comp M.ffEquiv.surjective
  rw [← genericPlaceInertiaHom_range X p.val (Q p) hsurj]
  ext g
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨placeInertiaConstantRootsEquiv K F Ω p.val (Q p) t, rfl⟩
  · rintro ⟨τ, rfl⟩
    obtain ⟨t, rfl⟩ := (placeInertiaConstantRootsEquiv K F Ω p.val (Q p)).surjective τ
    exact ⟨t, rfl⟩

include hfin in
/-- A second boundary point makes the actual global inertia parameter injective. -/
theorem boundaryPlaceInertiaLift_injective
    [Nontrivial (M.openBoundaryPlaces j)] (p : M.openBoundaryPlaces j) :
    Function.Injective (boundaryPlaceInertiaLift M j hj hfield Q p) := by
  intro x y h
  apply boundaryPlaceInertiaHom_injective M j hj hfield Q p
  exact congrArg (TopologicalAbelianization.mk _) h

include hfin hj hfield in
/-- Abelianization is injective on each original boundary inertia subgroup. -/
theorem boundaryInertia_abelianization_injOn
    [Nontrivial (M.openBoundaryPlaces j)] (p : M.openBoundaryPlaces j) :
    Set.InjOn (TopologicalAbelianization.mk
      (Aut (FiniteEtale.fiber (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X)))))
      (genericPlaceInertia X p.val (Q p) : Set _) := by
  intro x hx y hy h
  rw [← boundaryPlaceInertiaLift_range M j hj hfield Q p] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hab : a = b := boundaryPlaceInertiaHom_injective M j hj hfield Q p h
  exact congrArg (boundaryPlaceInertiaLift M j hj hfield Q p) hab

include hfin hj hfield in
/-- Every positive power of a nontrivial element of actual boundary inertia
remains nontrivial, in the original fundamental group. -/
theorem boundaryInertia_pow_ne_one
    [Nontrivial (M.openBoundaryPlaces j)] (p : M.openBoundaryPlaces j)
    {g : Aut (FiniteEtale.fiber (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X)))}
    (hg : g ∈ genericPlaceInertia X p.val (Q p)) (hg1 : g ≠ 1)
    {n : ℕ} (hn : n ≠ 0) : g ^ n ≠ 1 := by
  rw [← boundaryPlaceInertiaLift_range M j hj hfield Q p] at hg
  obtain ⟨t, rfl⟩ := hg
  have ht : t ≠ 1 := by
    intro h
    apply hg1
    rw [h, map_one]
  intro hpow
  apply primeToRoots_pow_ne_one K K ht hn
  apply boundaryPlaceInertiaLift_injective M j hj hfield Q p
  rw [map_pow, map_one]
  exact hpow

include hfin hj hfield in
/-- Positive powers of nontrivial boundary inertia remain visible in abelianization. -/
theorem boundaryInertia_abelianized_pow_ne_one
    [Nontrivial (M.openBoundaryPlaces j)] (p : M.openBoundaryPlaces j)
    {g : Aut (FiniteEtale.fiber
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X)))}
    (hg : g ∈ genericPlaceInertia X p.val (Q p)) (hg1 : g ≠ 1)
    {n : ℕ} (hn : n ≠ 0) :
    TopologicalAbelianization.mk _ (g ^ n) ≠ 1 := by
  intro h
  apply boundaryInertia_pow_ne_one M j hj hfield Q p hg hg1 hn
  apply boundaryInertia_abelianization_injOn M j hj hfield Q p
    ((genericPlaceInertia X p.val (Q p)).pow_mem hg n)
    (genericPlaceInertia X p.val (Q p)).one_mem
  simpa only [map_one] using h

end AnabelianGeometry.WeightFiltration
