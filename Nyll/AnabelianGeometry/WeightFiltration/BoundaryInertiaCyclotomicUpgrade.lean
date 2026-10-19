/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaEmbedding

/-! # BoundaryInertiaCyclotomicUpgrade -/

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

/-- Upgrade an abelian equality to the literal same-generator conjugation.
`v` is the geometric element supplied for the same arithmetic `gamma`.
The only subgroup preservation used is this gamma's normalizer membership. -/
theorem boundaryPlaceInertiaLift_conjugate_of_abelian_eq
    [Nontrivial (M.openBoundaryPlaces j)]
    (p : M.openBoundaryPlaces j)
    {P : Type*} [Group P]
    (i : Aut (FiniteEtale.fiber
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X))) →* P)
    (hi : Function.Injective i) (gamma : P)
    (hgamma : gamma ∈ Subgroup.normalizer
      ((genericPlaceInertia X p.val (Q p)).map i : Set P))
    (t t' : (primeToRootsSystem K K).inverseLimit)
    (v : Aut (FiniteEtale.fiber
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X))))
    (hv : i v = gamma * i (boundaryPlaceInertiaLift M j hj hfield Q p t) * gamma⁻¹)
    (hab : TopologicalAbelianization.mk _ v =
      boundaryPlaceInertiaHom M j hj hfield Q p t') :
    i (boundaryPlaceInertiaLift M j hj hfield Q p t') =
      gamma * i (boundaryPlaceInertiaLift M j hj hfield Q p t) * gamma⁻¹ := by
  let f := boundaryPlaceInertiaLift M j hj hfield Q p
  have hf (r : (primeToRootsSystem K K).inverseLimit) :
      f r ∈ genericPlaceInertia X p.val (Q p) := by
    rw [← boundaryPlaceInertiaLift_range M j hj hfield Q p]
    exact ⟨r, rfl⟩
  have hmem : i (f t) ∈ (genericPlaceInertia X p.val (Q p)).map i :=
    ⟨f t, hf t, rfl⟩
  have hconj := (Subgroup.mem_set_normalizer_iff.mp hgamma (i (f t))).mp hmem
  have hvI : v ∈ genericPlaceInertia X p.val (Q p) := by
    obtain ⟨w, hw, heq⟩ := hconj
    have hwv : w = v := hi (heq.trans hv.symm)
    exact hwv ▸ hw
  have hveq : v = f t' := by
    apply boundaryInertia_abelianization_injOn M j hj hfield Q p hvI (hf t')
    exact hab
  rw [← hveq]
  exact hv

end AnabelianGeometry.WeightFiltration
