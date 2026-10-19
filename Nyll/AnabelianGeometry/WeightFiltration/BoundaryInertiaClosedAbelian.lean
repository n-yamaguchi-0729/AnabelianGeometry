/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaEmbedding

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
    (M : CurveModel K F)
    {X : Scheme} [IsIntegral X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    [Algebra F X.functionField]
    (hfield : algebraMap F X.functionField = (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring F Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal]


include hj hfield in
/-- Original boundary inertia is closed in the actual fundamental group. -/
theorem boundaryInertia_isClosed (p : M.openBoundaryPlaces j) :
    IsClosed (genericPlaceInertia X p.val (Q p) : Set
      (Aut (FiniteEtale.fiber
        (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
          X.fromSpecStalk (genericPoint X))))) := by
  rw [← boundaryPlaceInertiaLift_range M j hj hfield Q p]
  exact (boundaryPlaceInertiaLift M j hj hfield Q p).continuous_toFun.isClosedMap.isClosed_range

include hj hfield in
/-- Original boundary inertia is commutative inside the actual fundamental group. -/
theorem boundaryInertia_mul_comm (p : M.openBoundaryPlaces j)
    {x y : Aut (FiniteEtale.fiber
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X)))}
    (hx : x ∈ genericPlaceInertia X p.val (Q p))
    (hy : y ∈ genericPlaceInertia X p.val (Q p)) : x * y = y * x := by
  rw [← boundaryPlaceInertiaLift_range M j hj hfield Q p] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hab : a * b = b * a := by
    apply (primeToRootsSystem K K).ext
    intro n
    exact mul_comm (show rootsOfUnity n.val K from a.val n)
      (show rootsOfUnity n.val K from b.val n)
  rw [← map_mul, hab, map_mul]

end AnabelianGeometry.WeightFiltration
