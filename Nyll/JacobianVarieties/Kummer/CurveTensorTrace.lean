/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Kummer.FiniteAdicH1
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalAdicCup
public import Nyll.EtaleCohomology.Classical.RationalGraphCup
public import Nyll.EtaleCohomology.Classical.RationalKunnethMap
public import Nyll.JacobianVarieties.Kummer.CurveNativeAdicH2
public import Nyll.JacobianVarieties.Kummer.CurveNativeCupDuality
public import Nyll.JacobianVarieties.Kummer.CurveNativeCupPairing
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Trace

/-!
# Graph degrees and traces of actual H¹ tensors

The native cup pairing assigns to `x ⊗ y` the rank-one operator
`z ↦ deg(z ∪ y) • x` on the original rational étale H¹. Its trace after
an endomorphism `A` is `deg(A x ∪ y)`. Thus the degree of graph pullback
on the actual middle Künneth map is the trace of this operator composed
with the original cohomological pullback.

The finite-dimensionality needed for trace is supplied by the curve.
No perfectness of the cup pairing is needed for this calculation. The
geometric assertion that the normalized diagonal comes from an H¹
tensor inducing minus the identity remains a separate comparison.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory
open EtaleCohomology.Classical
open scoped TensorProduct

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

local notation "H" => rationalEllAdicCohomology ℓ M.C 1

/-- Contract the second factor of an original H¹ tensor with native
cup and degree, retaining its first factor as the output vector. -/
def nativeRationalH1TensorAction :
    (H ⊗[ℚ_[ℓ]] H) →ₗ[ℚ_[ℓ]] Module.End ℚ_[ℓ] H :=
  (dualTensorHom ℚ_[ℓ] H H).comp
    ((TensorProduct.map (M.nativeRationalEllAdicCupPairing ℓ hℓ 1 1 rfl).flip
      (LinearMap.id : H →ₗ[ℚ_[ℓ]] H)).comp
        (TensorProduct.comm ℚ_[ℓ] H H).toLinearMap)

/-- The proved native H¹ duality makes the original contraction an
isomorphism from tensors to endomorphisms. -/
def nativeRationalH1TensorActionEquiv :
    (H ⊗[ℚ_[ℓ]] H) ≃ₗ[ℚ_[ℓ]] Module.End ℚ_[ℓ] H := by
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have : FiniteDimensional ℚ_[ℓ] H := M.finiteDimensional_rationalEllAdicH1 ℓ hℓ
  let e : H ≃ₗ[ℚ_[ℓ]] Module.Dual ℚ_[ℓ] H :=
    LinearMap.BilinForm.toDual
      (M.nativeRationalEllAdicCupPairing ℓ hℓ 1 1 rfl).flip
      (LinearMap.BilinForm.Nondegenerate.flip
        (M.nativeRationalEllAdicCupPairing_one_one_nondegenerate ℓ hℓ))
  exact (TensorProduct.comm ℚ_[ℓ] H H).trans
    ((TensorProduct.congr e (LinearEquiv.refl ℚ_[ℓ] H)).trans
      (dualTensorHomEquiv ℚ_[ℓ] H H))

/-- The tensor equivalence retains the original cup contraction. -/
theorem nativeRationalH1TensorActionEquiv_toLinearMap :
    (M.nativeRationalH1TensorActionEquiv ℓ hℓ).toLinearMap =
      M.nativeRationalH1TensorAction ℓ hℓ := rfl

/-- The unique tensor whose original cup contraction is minus the identity.
Its identification with the geometric diagonal is a separate assertion. -/
def nativeRationalH1NegativeIdentityTensor : H ⊗[ℚ_[ℓ]] H :=
  (M.nativeRationalH1TensorActionEquiv ℓ hℓ).symm
    (-(LinearMap.id : Module.End ℚ_[ℓ] H))

/-- The canonical negative identity tensor has its defining actual action. -/
theorem nativeRationalH1NegativeIdentityTensor_action :
    M.nativeRationalH1TensorAction ℓ hℓ (M.nativeRationalH1NegativeIdentityTensor ℓ hℓ) =
      -(LinearMap.id : Module.End ℚ_[ℓ] H) :=
  (M.nativeRationalH1TensorActionEquiv ℓ hℓ).apply_symm_apply _

/-- A pure tensor gives the rank-one map defined by the actual cup
pairing, with the order of its two cup arguments explicit. -/
theorem nativeRationalH1TensorAction_tmul (x y : H) :
    M.nativeRationalH1TensorAction ℓ hℓ (x ⊗ₜ[ℚ_[ℓ]] y) =
      ((M.nativeRationalEllAdicCupPairing ℓ hℓ 1 1 rfl).flip y).smulRight x := by
  apply LinearMap.ext
  intro z
  simp only [nativeRationalH1TensorAction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
    dualTensorHom_apply, LinearMap.smulRight_apply]

/-- Trace of contraction against an actual H¹ tensor is the native
degree of cup after applying the given endomorphism to its first factor. -/
theorem nativeRationalH1TensorAction_trace_comp (A : Module.End ℚ_[ℓ] H)
    (t : H ⊗[ℚ_[ℓ]] H) :
    LinearMap.trace ℚ_[ℓ] H (A.comp (M.nativeRationalH1TensorAction ℓ hℓ t)) =
      M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        (TensorProduct.lift ((rationalEllAdicCup M.C ℓ 1 1 2 rfl).compl₁₂
          A (LinearMap.id : H →ₗ[ℚ_[ℓ]] H)) t) := by
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have : FiniteDimensional ℚ_[ℓ] H := M.finiteDimensional_rationalEllAdicH1 ℓ hℓ
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
      have hcomp :
          A.comp (M.nativeRationalH1TensorAction ℓ hℓ (x ⊗ₜ[ℚ_[ℓ]] y)) =
            ((M.nativeRationalEllAdicCupPairing ℓ hℓ 1 1 rfl).flip y).smulRight
              (A x) := by
        rw [nativeRationalH1TensorAction_tmul]
        apply LinearMap.ext
        intro z
        exact A.map_smul
          ((M.nativeRationalEllAdicCupPairing ℓ hℓ 1 1 rfl).flip y z) x
      rw [hcomp, LinearMap.trace_smulRight]
      rfl
  | add s t hs ht =>
      rw [map_add, LinearMap.comp_add, map_add, map_add, map_add, hs, ht]

/-- On the original middle Künneth map, graph pullback followed by
native degree is the trace of the original H¹ pullback composed with
the tensor's native cup contraction. -/
theorem nativeRationalH1TensorAction_graph_degree_over
    {S : Scheme.{u}} (b : M.C ⟶ S) (v : M.C ⟶ M.C) (hv : v ≫ b = b)
    (t : H ⊗[ℚ_[ℓ]] H) :
    M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        (rationalEllAdicCohomologyPullback ℓ (graphOver b v hv) 2
          (rationalEllAdicKunnethComponent ℓ b b 1 1 2 rfl t)) =
      LinearMap.trace ℚ_[ℓ] H
        ((rationalEllAdicCohomologyPullback ℓ v 1).comp
          (M.nativeRationalH1TensorAction ℓ hℓ t)) := by
  rw [nativeRationalH1TensorAction_trace_comp]
  exact congrArg (M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ)
    (LinearMap.congr_fun
      (rationalEllAdicKunnethComponent_graphOver ℓ b b v hv
        1 1 2 rfl) t)

/-- The actual graph degree of the canonical negative identity tensor is
minus the trace of the original H¹ pullback. -/
theorem nativeRationalH1NegativeIdentityTensor_graph_degree_over
    {S : Scheme.{u}} (b : M.C ⟶ S) (v : M.C ⟶ M.C) (hv : v ≫ b = b) :
    M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        (rationalEllAdicCohomologyPullback ℓ (graphOver b v hv) 2
          (rationalEllAdicKunnethComponent ℓ b b 1 1 2 rfl
            (M.nativeRationalH1NegativeIdentityTensor ℓ hℓ))) =
      -LinearMap.trace ℚ_[ℓ] H (rationalEllAdicCohomologyPullback ℓ v 1) := by
  rw [nativeRationalH1TensorAction_graph_degree_over,
    nativeRationalH1NegativeIdentityTensor_action,
    LinearMap.comp_neg, LinearMap.comp_id, map_neg]

/-- On the original middle Künneth map, graph pullback followed by
native degree is the trace of the original H¹ pullback composed with
the tensor's native cup contraction. -/
theorem nativeRationalH1TensorAction_graph_degree
    (v : M.C ⟶ M.C) (hv : v ≫ M.toBase = M.toBase)
    (t : H ⊗[ℚ_[ℓ]] H) :
    M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        (rationalEllAdicCohomologyPullback ℓ (graphOver M.toBase v hv) 2
          (rationalEllAdicKunnethComponent ℓ M.toBase M.toBase 1 1 2 rfl t)) =
      LinearMap.trace ℚ_[ℓ] H
        ((rationalEllAdicCohomologyPullback ℓ v 1).comp
          (M.nativeRationalH1TensorAction ℓ hℓ t)) :=
  M.nativeRationalH1TensorAction_graph_degree_over ℓ hℓ M.toBase v hv t

/-- The actual graph degree of the canonical negative identity tensor is
minus the trace of the original H¹ pullback. -/
theorem nativeRationalH1NegativeIdentityTensor_graph_degree
    (v : M.C ⟶ M.C) (hv : v ≫ M.toBase = M.toBase) :
    M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        (rationalEllAdicCohomologyPullback ℓ (graphOver M.toBase v hv) 2
          (rationalEllAdicKunnethComponent ℓ M.toBase M.toBase 1 1 2 rfl
            (M.nativeRationalH1NegativeIdentityTensor ℓ hℓ))) =
      -LinearMap.trace ℚ_[ℓ] H (rationalEllAdicCohomologyPullback ℓ v 1) :=
  M.nativeRationalH1NegativeIdentityTensor_graph_degree_over ℓ hℓ M.toBase v hv

end AlgebraicCurve.CurveModel
