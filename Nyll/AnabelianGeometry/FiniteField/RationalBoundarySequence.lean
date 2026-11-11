/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.EllAdicBoundarySequence
public import Nyll.EtaleCohomology.Frobenius.Adic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The actual rational boundary quotient

Scalar extension of the proved integral residue sequence identifies the
quotient of the original open-curve rational H¹ by the original proper image.
Right exactness applies to the constructed surjective residue map, including
an empty boundary. No exactness or comparison is an input.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open EtaleCohomology.Classical
open scoped TensorProduct

namespace AnabelianGeometry.FiniteField

variable {K : Type uGeom} {F : Type uField₁} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [Algebra.EssFiniteType K F] [IsCurveOver K F]
  (M : CurveModel K F)
  {X : Scheme.{uGeom}} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  {Ω : Type uGeom} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- Scalar extension of the original integral residue map. -/
def rationalEllAdicBoundaryMap :
    rationalEllAdicCohomology ℓ X 1 →ₗ[ℚ_[ℓ]]
      ℚ_[ℓ] ⊗[ℤ_[ℓ]] ellAdicBoundarySpace M j ℓ :=
  (ellAdicBoundaryMap M j hj ξ ℓ hℓ).baseChange ℚ_[ℓ]

omit [Algebra.EssFiniteType K F] in
/-- Pure tensors retain the original integral boundary value. -/
theorem rationalEllAdicBoundaryMap_tmul (r : ℚ_[ℓ]) (a : ellAdicCohomology X ℓ 1) :
    rationalEllAdicBoundaryMap M j hj ξ ℓ hℓ (r ⊗ₜ[ℤ_[ℓ]] a) =
      r ⊗ₜ[ℤ_[ℓ]] ellAdicBoundaryMap M j hj ξ ℓ hℓ a := rfl

/-- The actual rational residue map is surjective. -/
theorem rationalEllAdicBoundaryMap_surjective :
    Function.Surjective (rationalEllAdicBoundaryMap M j hj ξ ℓ hℓ) :=
  LinearMap.baseChange_surjective ℚ_[ℓ]
    (ellAdicBoundaryMap_surjective M j hj ξ ℓ hℓ)

/-- Rational boundary exactness retains the original compactification map. -/
theorem range_rationalEllAdicPullback_eq_ker_boundaryMap :
    LinearMap.range (rationalEllAdicPullback j ℓ 1) =
      LinearMap.ker (rationalEllAdicBoundaryMap M j hj ξ ℓ hℓ) := by
  have hex : Function.Exact (ellAdicPullback j ℓ 1)
      (ellAdicBoundaryMap M j hj ξ ℓ hℓ) :=
    LinearMap.exact_iff.mpr
      (range_ellAdicPullback_eq_ker_boundaryMap M j hj ξ ℓ hℓ).symm
  have ht := lTensor_exact ℚ_[ℓ] hex
    (ellAdicBoundaryMap_surjective M j hj ξ ℓ hℓ)
  ext a
  exact (ht a).symm

/-- The quotient by the original proper H¹ image is the scalar extension of
the actual sum-zero integral boundary vectors. -/
def rationalBoundaryQuotientEquiv :
    (rationalEllAdicCohomology ℓ X 1 ⧸ LinearMap.range (rationalEllAdicPullback j ℓ 1)) ≃ₗ[ℚ_[ℓ]]
      ℚ_[ℓ] ⊗[ℤ_[ℓ]] ellAdicBoundarySpace M j ℓ :=
  (Submodule.quotEquivOfEq _ _
    (range_rationalEllAdicPullback_eq_ker_boundaryMap M j hj ξ ℓ hℓ)).trans
      ((rationalEllAdicBoundaryMap M j hj ξ ℓ hℓ).quotKerEquivOfSurjective
        (rationalEllAdicBoundaryMap_surjective M j hj ξ ℓ hℓ))

/-- The quotient comparison is induced by the original residue map. -/
theorem rationalBoundaryQuotientEquiv_mk (a : rationalEllAdicCohomology ℓ X 1) :
    rationalBoundaryQuotientEquiv M j hj ξ ℓ hℓ (Submodule.Quotient.mk a) =
      rationalEllAdicBoundaryMap M j hj ξ ℓ hℓ a := rfl

end AnabelianGeometry.FiniteField
