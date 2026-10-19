/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaPrimeIndependence
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaEmbedding
import Mathlib.Logic.Function.Basic

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

local notation "G" => Aut (FiniteEtale.fiber
  (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
    X.fromSpecStalk (genericPoint X)))

/-- Any maximal prime above the same place gives the fixed abelianized coordinate range. -/
theorem boundaryInertia_abelianized_range_eq_coordinate_of_maximal
    (p : M.openBoundaryPlaces j)
    (q : Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [q.IsMaximal] :
    (genericPlaceInertia X p.val q).map (TopologicalAbelianization.mk G) =
      (boundaryPlaceInertiaHom M j hj hfield Q p).toMonoidHom.range := by
  classical
  let Qp : ∀ r : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat r.val.toValuationSubring Ω) :=
    Function.update Q p q
  let : ∀ r, (Qp r).IsMaximal := by
    intro r
    by_cases h : r = p
    · subst r
      simpa only [Qp, Function.update_self] using (inferInstance : q.IsMaximal)
    · simpa only [Qp, Function.update_of_ne h] using
        (inferInstance : (Q r).IsMaximal)
  have hp : Qp p = q := Function.update_self p q Q
  have hhom :
      (boundaryPlaceInertiaHom M j hj hfield Qp p).toMonoidHom =
        (boundaryPlaceInertiaHom M j hj hfield Q p).toMonoidHom := by
    ext t
    exact boundaryPlaceInertiaHom_independent_of_primes M j hj hfield Qp Q p t
  calc
    (genericPlaceInertia X p.val q).map (TopologicalAbelianization.mk G) =
        (boundaryPlaceInertiaHom M j hj hfield Qp p).toMonoidHom.range := by
      simpa only [hp] using
        (boundaryPlaceInertiaHom_range M j hj hfield Qp p).symm
    _ = (boundaryPlaceInertiaHom M j hj hfield Q p).toMonoidHom.range := by
      rw [hhom]

include Q hj hfield in
/-- The injective abelian image does not depend on the chosen maximal prime. -/
theorem boundaryInertia_abelianization_injOn_of_maximal
    [IsCurveOver K F] [Finite (M.openBoundaryPlaces j)]
    [Nontrivial (M.openBoundaryPlaces j)]
    (p : M.openBoundaryPlaces j)
    (q : Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [q.IsMaximal] :
    Set.InjOn (TopologicalAbelianization.mk G)
      (genericPlaceInertia X p.val q : Set G) := by
  classical
  let Qp : ∀ r : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat r.val.toValuationSubring Ω) :=
    Function.update Q p q
  let : ∀ r, (Qp r).IsMaximal := by
    intro r
    by_cases h : r = p
    · subst r
      simpa only [Qp, Function.update_self] using (inferInstance : q.IsMaximal)
    · simpa only [Qp, Function.update_of_ne h] using
        (inferInstance : (Q r).IsMaximal)
  have hp : Qp p = q := Function.update_self p q Q
  simpa only [hp] using
    (boundaryInertia_abelianization_injOn M j hj hfield Qp p)

end AnabelianGeometry.WeightFiltration
