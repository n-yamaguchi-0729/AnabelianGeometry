/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.SuppliedClosureComparison
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceBasePointComparison
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisNaturality

/-!
# Original field-source maps under a specified separable-closure equivalence

Extension of field-valued points along the actual closure equivalence gives
the comparison of the original scheme fibers. On absolute automorphisms the
comparison is precisely conjugation by that equivalence. In particular the
native separable closure and a constant cover's supplied ambient closure can
be compared without an unspecified change of the original Galois map.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {F Ω₀ Ω : Type u} [Field F] [Field Ω₀] [Field Ω]
  [Algebra F Ω₀] [Algebra F Ω] [IsSepClosure F Ω₀] [IsSepClosure F Ω]
  [IsSepClosed Ω₀] [IsSepClosed Ω]
  {X : Scheme.{u}} (p : Spec (.of F) ⟶ X) (e : Ω₀ ≃ₐ[F] Ω)

/-- The comparison induced by extension of actual field-valued points
along the specified separable-closure equivalence. -/
def fieldSourceClosureFiberIso :
    fiber (ξ F Ω₀ ≫ p) ≅ fiber (ξ F Ω ≫ p) :=
  (pullbackFiberIso p (ξ F Ω₀)).symm ≪≫
    Functor.isoWhiskerLeft (pullback p) (suppliedClosureFieldFiberIso e) ≪≫
      pullbackFiberIso p (ξ F Ω)

/-- The original pointed fundamental groups under the same actual
separable-closure comparison. -/
def fieldSourceClosureGroupEquiv : π₁ᵉᵗ(ξ F Ω₀ ≫ p) ≃ₜ* π₁ᵉᵗ(ξ F Ω ≫ p) :=
  continuousConjAut (fieldSourceClosureFiberIso p e)

/-- The original field-source Galois homomorphisms are intertwined by
literal conjugation of field automorphisms by the supplied equivalence. -/
theorem fieldSourceClosureGroupEquiv_galois [IsIntegral X] (σ : Gal(Ω₀/F)) :
    fieldSourceClosureGroupEquiv p e (fieldSourceAbsoluteGaloisHom F Ω₀ p σ) =
      fieldSourceAbsoluteGaloisHom F Ω p (AlgEquiv.autCongr e σ) := by
  have h := fundamentalGroupHom_conjAut p (ξ F Ω₀) (ξ F Ω)
    (suppliedClosureFieldFiberIso e) (suppliedGaloisEquivFundamentalGroup F Ω₀ σ)
  rw [suppliedClosureFieldFiberIso_galois] at h
  exact h

/-- Equality of the actual geometric points compares the supplied field-source
Galois maps through literal scalar restriction. -/
theorem fieldSourceAbsoluteGaloisHom_eqToIso
    (K F Ω : Type u) [Field K] [Field F] [Field Ω]
    [Algebra K F] [Algebra K Ω] [Algebra F Ω] [IsScalarTower K F Ω]
    [IsSepClosure K Ω] [IsSepClosure F Ω] [IsSepClosed Ω]
    {U : Scheme.{u}} [IsIntegral U]
    (p : Spec (.of F) ⟶ U) (p₀ : Spec (.of K) ⟶ U)
    (hpoint : ξ F Ω ≫ p = ξ K Ω ≫ p₀) (σ : Gal(Ω/F)) :
    continuousConjAut (eqToIso (congrArg fiber hpoint))
        (fieldSourceAbsoluteGaloisHom F Ω p σ) =
      fieldSourceAbsoluteGaloisHom K Ω p₀ (σ.restrictScalars K) := by
  have hF := fundamentalGroupHom_point_of_point_action
    p (ξ F Ω) (suppliedGaloisEquivFundamentalGroup F Ω σ)
    σ.toRingHom (suppliedGaloisEquivFundamentalGroup_point F Ω σ)
  have hK := fundamentalGroupHom_point_of_point_action
    p₀ (ξ K Ω)
    (suppliedGaloisEquivFundamentalGroup K Ω (σ.restrictScalars K))
    (σ.restrictScalars K).toRingHom
    (suppliedGaloisEquivFundamentalGroup_point K Ω (σ.restrictScalars K))
  apply Aut.ext
  ext Z z
  apply (fiberObjEquivHom (ξ K Ω ≫ p₀) Z).injective
  apply Over.OverMorphism.ext
  exact (point_action_of_eqToIso hpoint _ σ.toRingHom hF Z z).trans (hK Z z).symm

end AlgebraicGeometry.FiniteEtale
