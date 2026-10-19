/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaGeneration
import Nyll.EtaleFundamentalGroups.Inertia.GenericPlaceInertiaHom
import Nyll.AnabelianGeometry.WeightFiltration.PlaceInertiaConstantRoots
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Topology.Algebra.Monoid

/-!
# The actual boundary inertia map

Common constant roots parametrize each original place inertia. Their finite
product maps continuously onto the actual abelian compactification kernel.
The product construction and its range formula reuse the finite coproduct API.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

private def continuousPiCoprod
    {ι T G : Type*} [Fintype ι] [Group T] [TopologicalSpace T]
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : ι → T →ₜ* G) : (ι → T) →ₜ* G := by
  refine
    { toMonoidHom := MonoidHom.noncommPiCoprod (fun i => (f i).toMonoidHom)
        (fun _ _ _ _ _ => Commute.all _ _)
      continuous_toFun := ?_ }
  change Continuous (fun x : ι → T => Finset.univ.noncommProd
    (fun i => f i (x i)) (fun _ _ _ _ _ => Commute.all _ _))
  simp only [Finset.noncommProd_eq_prod]
  apply continuous_finsetProd
  intro i _
  exact (f i).continuous_toFun.comp (continuous_apply i)

variable
    {K F : Type} [Field K] [CharZero K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
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
    [Fintype (M.openBoundaryPlaces j)]

/-- One original boundary inertia, with the common constant-root parameter. -/
def boundaryPlaceInertiaHom (p : M.openBoundaryPlaces j) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    (primeToRootsSystem K K).inverseLimit →ₜ*
      TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) := by
  intro η ξ
  have hsurj : Function.Surjective (algebraMap F X.functionField) := by
    rw [hfield]
    exact (j.functionFieldRingEquivOfIsOpenImmersion).surjective.comp M.ffEquiv.surjective
  exact (TopologicalAbelianization.mkₜ (Aut (FiniteEtale.fiber ξ))).comp
    ((genericPlaceInertiaHom X p.val (Q p) hsurj).comp
      (ContinuousMonoidHom.toContinuousMonoidHom
        (placeInertiaConstantRootsEquiv K F Ω p.val (Q p))))

omit [Fintype (M.openBoundaryPlaces j)] [Algebra.EssFiniteType K F]
  [IsCurveOver K F] [CompactSpace X] [Algebra K Ω]
  [∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω] in
/-- Each coordinate has the original boundary-inertia image in the actual abelianization. -/
theorem boundaryPlaceInertiaHom_range (p : M.openBoundaryPlaces j) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    (boundaryPlaceInertiaHom M j hj hfield Q p).toMonoidHom.range =
      (genericPlaceInertia X p.val (Q p)).map
        (TopologicalAbelianization.mk (Aut (FiniteEtale.fiber ξ))) := by
  intro η ξ
  have hsurj : Function.Surjective (algebraMap F X.functionField) := by
    rw [hfield]
    exact (j.functionFieldRingEquivOfIsOpenImmersion).surjective.comp M.ffEquiv.surjective
  rw [← genericPlaceInertiaHom_range X p.val (Q p) hsurj]
  ext g
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨genericPlaceInertiaHom X p.val (Q p) hsurj
      (placeInertiaConstantRootsEquiv K F Ω p.val (Q p) t),
      ⟨placeInertiaConstantRootsEquiv K F Ω p.val (Q p) t, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨τ, rfl⟩, rfl⟩
    obtain ⟨t, ht⟩ := (placeInertiaConstantRootsEquiv K F Ω p.val (Q p)).surjective τ
    refine ⟨t, ?_⟩
    change TopologicalAbelianization.mk _
      (genericPlaceInertiaHom X p.val (Q p) hsurj
        (placeInertiaConstantRootsEquiv K F Ω p.val (Q p) t)) = _
    rw [ht]
    rfl

/-- Multiply the boundary inertia images using one common constant-root parameter per place. -/
def boundaryInertiaMap :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    (M.openBoundaryPlaces j → (primeToRootsSystem K K).inverseLimit) →ₜ*
      TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) :=
  continuousPiCoprod (boundaryPlaceInertiaHom M j hj hfield Q)

/-- The product map reaches exactly the actual abelian compactification kernel. -/
theorem boundaryInertiaMap_range :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    (boundaryInertiaMap M j hj hfield Q).toMonoidHom.range =
      (compactificationAbelianizationMap j ξ).toMonoidHom.ker := by
  intro η ξ
  let f := boundaryInertiaMap M j hj hfield Q
  have hr : f.toMonoidHom.range =
      ⨆ p : M.openBoundaryPlaces j, (genericPlaceInertia X p.val (Q p)).map
        (TopologicalAbelianization.mk (Aut (FiniteEtale.fiber ξ))) := by
    exact (MonoidHom.noncommPiCoprod_range
      (fun p => (boundaryPlaceInertiaHom M j hj hfield Q p).toMonoidHom)
      (hcomm := fun _ _ _ _ _ => Commute.all _ _)).trans
        (iSup_congr (fun p => boundaryPlaceInertiaHom_range M j hj hfield Q p))
  have hclosed : IsClosed (Set.range f) :=
    f.continuous_toFun.isClosedMap.isClosed_range
  rw [compactificationAbelianization_ker_eq_boundaryInertia_closure M j hj hfield Q, ← hr]
  exact le_antisymm f.toMonoidHom.range.le_topologicalClosure
    (f.toMonoidHom.range.topologicalClosure_minimal le_rfl hclosed)

end AnabelianGeometry.WeightFiltration
