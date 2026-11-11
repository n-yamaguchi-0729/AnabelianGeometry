/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AlgebraicClosureAction
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison

/-!
# Detecting actual finite H¹ classes at a normal separably closed generic point

The normal overfield can be an actual algebraic closure in every
characteristic. The actual field action determines the global H¹ class
through its proved surjectivity on the original geometric fibre.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

/-- Every automorphism of the geometric generic fibre of a normal integral
scheme comes from a field automorphism of its chosen normal separably
closed overfield. In particular, a genuine algebraic closure is allowed. -/
theorem genericFieldAction_surjective
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosed Ω] [Normal X.functionField Ω] :
    Function.Surjective (fun σ : Ω ≃ₐ[X.functionField] Ω =>
      fundamentalGroupHom (X.fromSpecStalk (genericPoint X))
        (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)))
        (toAut (fib X.functionField Ω) (Ω ≃ₐ[X.functionField] Ω) σ)) := by
  let j := X.fromSpecStalk (genericPoint X)
  let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
  have : QuasiCompact j :=
    { isCompact_preimage := fun U _ _ => (Set.toFinite (j ⁻¹' U)).isCompact }
  have : IsDominant j := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro x
    apply (genericPoint_specializes x).mem_closed isClosed_closure
    exact subset_closure ⟨IsLocalRing.closedPoint (CommRingCat.of X.functionField),
      Scheme.fromSpecStalk_closedPoint (X := X) (x := genericPoint X)⟩
  have hj := fundamentalGroupHom_surjective_of_isPreimmersion_of_isDominant j η
  exact hj.comp (normalFieldAction_toAut_surjective X.functionField Ω)

end AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.Cohomology

/-- Equality of actual finite H¹ classes is detected by their characters
on field automorphisms at any chosen normal separably closed generic point. -/
theorem finiteH1_ext_genericFieldAction
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosed Ω] [Normal X.functionField Ω]
    (A : AddCommGrpCat.{u}) [Finite A]
    (a b : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    (∀ σ : Ω ≃ₐ[X.functionField] Ω,
      (finiteH1CharacterEquiv A ξ a).toMul
          (FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
            (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ)) =
      (finiteH1CharacterEquiv A ξ b).toMul
          (FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
            (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ))) ->
      a = b := by
  intro η ξ htop hdiscrete h
  apply (finiteH1CharacterEquiv A ξ).injective
  apply ContinuousMonoidHom.ext
  intro g
  obtain ⟨σ, rfl⟩ := FiniteEtale.genericFieldAction_surjective X Ω g
  exact h σ

end EtaleFundamentalGroups.Cohomology
