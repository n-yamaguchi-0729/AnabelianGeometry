/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaEmbedding
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsProcyclic

/-! # Procyclicity and nontriviality of actual boundary inertia -/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia ProCGroups.Generation

namespace AnabelianGeometry.WeightFiltration

variable
    {K F : Type} [Field K] [CharZero K] [IsAlgClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F)
    {X : Scheme} [IsIntegral X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    [Algebra F X.functionField]
    (hfield : algebraMap F X.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring F Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal]

local notation "G" => Aut (FiniteEtale.fiber
  (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
    X.fromSpecStalk (genericPoint X)))

include hj hfield in
/-- Actual boundary inertia is generated topologically by one element. -/
theorem boundaryInertia_eq_topologicalClosure_zpowers (p : M.openBoundaryPlaces j) :
    ∃ z : G, (Subgroup.zpowers z).topologicalClosure =
      genericPlaceInertia X p.val (Q p) := by
  obtain ⟨t, ht⟩ := primeToRoots_exists_topological_generator K K
  let f := boundaryPlaceInertiaLift M j hj hfield Q p
  refine ⟨f t, ?_⟩
  exact (topologicalClosure_zpowers_image_eq_range f t ht).trans
    (boundaryPlaceInertiaLift_range M j hj hfield Q p)

include hj hfield in
/-- Each conjugate actual boundary inertia is also procyclic. -/
theorem boundaryInertia_conjugate_eq_topologicalClosure_zpowers
    (p : M.openBoundaryPlaces j) (a : G) :
    ∃ z : G, (Subgroup.zpowers z).topologicalClosure =
      (genericPlaceInertia X p.val (Q p)).map (MulAut.conj a).toMonoidHom := by
  obtain ⟨t, ht⟩ := primeToRoots_exists_topological_generator K K
  let f := boundaryPlaceInertiaLift M j hj hfield Q p
  let c : G →ₜ* G :=
    { toMonoidHom := (MulAut.conj a).toMonoidHom
      continuous_toFun := by
        change Continuous (fun b : G => a * b * a⁻¹)
        exact IsTopologicalGroup.continuous_conj a }
  have hrange : (c.comp f).toMonoidHom.range =
      (genericPlaceInertia X p.val (Q p)).map (MulAut.conj a).toMonoidHom := by
    rw [← boundaryPlaceInertiaLift_range M j hj hfield Q p]
    change (c.comp f).toMonoidHom.range = f.toMonoidHom.range.map c.toMonoidHom
    ext b
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨f s, ⟨s, rfl⟩, rfl⟩
    · rintro ⟨s, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, rfl⟩
  exact ⟨(c.comp f) t,
    (topologicalClosure_zpowers_image_eq_range (c.comp f) t ht).trans hrange⟩

variable [IsCurveOver K F] [CompactSpace X] [Algebra K Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω]
    [hfin : Finite (M.openBoundaryPlaces j)] [Nontrivial (M.openBoundaryPlaces j)]

include hfin hj hfield in
/-- At least two boundary places make actual boundary inertia nontrivial. -/
theorem boundaryInertia_exists_ne_one (p : M.openBoundaryPlaces j) :
    ∃ z : G, z ∈ genericPlaceInertia X p.val (Q p) ∧ z ≠ 1 := by
  obtain ⟨t, ht⟩ := primeToRoots_exists_ne_one K K
  let f := boundaryPlaceInertiaLift M j hj hfield Q p
  refine ⟨f t, ?_, ?_⟩
  · rw [← boundaryPlaceInertiaLift_range M j hj hfield Q p]
    exact ⟨t, rfl⟩
  · intro h
    apply ht
    apply boundaryPlaceInertiaLift_injective M j hj hfield Q p
    simpa only [map_one] using h

include hfin hj hfield in
/-- The same nontriviality holds after conjugation. -/
theorem boundaryInertia_conjugate_exists_ne_one
    (p : M.openBoundaryPlaces j) (a : G) :
    ∃ z : G, z ∈ (genericPlaceInertia X p.val (Q p)).map
      (MulAut.conj a).toMonoidHom ∧ z ≠ 1 := by
  obtain ⟨x, hx, hx1⟩ := boundaryInertia_exists_ne_one M j hj hfield Q p
  refine ⟨(MulAut.conj a) x, ⟨x, hx, rfl⟩, ?_⟩
  intro h
  apply hx1
  apply (MulAut.conj a).injective
  simpa only [map_one] using h

end AnabelianGeometry.WeightFiltration
