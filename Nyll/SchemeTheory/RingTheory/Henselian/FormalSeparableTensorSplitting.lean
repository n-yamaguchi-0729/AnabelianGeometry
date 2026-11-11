/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Henselian.FiniteSeparableFormalLiftEmbedding
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.TensorProduct.Basic

/-! # Splitting a deformed finite separable algebra over a formal disc

Each residue embedding lifts through the actual finite separable extension.
Evaluation in these lifts splits the deformed tensor product into copies of
the power-series ring. In a primitive-element basis the evaluation matrix is
Vandermonde. Its determinant is a unit because its constant coefficient is
the nonzero Vandermonde determinant of the distinct residue embeddings.

The scalar structure on power series is the given deformation `τ`. No tower
through the constant embedding of the coefficient field is installed.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace PowerSeries

variable {E F Ω : Type*} [Field E] [Field F] [Field Ω]
  [Algebra E F] [Algebra E Ω]
  [FiniteDimensional E F] [Algebra.IsSeparable E F]

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] in
/-- A residue-field embedding is compatible with the given base-ring reduction. -/
theorem embedding_residue_compat
    (τ : E →+* PowerSeries Ω)
    (hτ : constantCoeff.comp τ = algebraMap E Ω)
    (ι : F →ₐ[E] Ω) :
    constantCoeff.comp τ = ι.toRingHom.comp (algebraMap E F) := by
  apply RingHom.ext
  intro a
  exact (RingHom.congr_fun hτ a).trans (ι.commutes a).symm

/-- The actual formal lift of a residue embedding through a finite
separable extension, constructed by the simple-root lifting theorem. -/
def formalEmbeddingLift
    (τ : E →+* PowerSeries Ω)
    (hτ : constantCoeff.comp τ = algebraMap E Ω)
    (ι : F →ₐ[E] Ω) : F →+* PowerSeries Ω :=
  Classical.choose (existsUnique_formalLift_finiteSeparable_embedding
    ι.toRingHom τ (embedding_residue_compat τ hτ ι)).exists

/-- The constructed lift extends the given deformation and reduces to
the original residue embedding. -/
theorem formalEmbeddingLift_spec
    (τ : E →+* PowerSeries Ω)
    (hτ : constantCoeff.comp τ = algebraMap E Ω)
    (ι : F →ₐ[E] Ω) :
    (formalEmbeddingLift τ hτ ι).comp (algebraMap E F) = τ ∧
      constantCoeff.comp (formalEmbeddingLift τ hτ ι) = ι.toRingHom :=
  Classical.choose_spec (existsUnique_formalLift_finiteSeparable_embedding
    ι.toRingHom τ (embedding_residue_compat τ hτ ι)).exists

variable [IsAlgClosed Ω]

/-- The deformed scalar extension is actually split by evaluation in the
formal lifts of all residue embeddings. The displayed formula retains the
chosen embeddings, rather than merely exhibiting an unlabelled product. -/
theorem exists_formalTensorProductEquiv
    (τ : E →+* PowerSeries Ω)
    (hτ : constantCoeff.comp τ = algebraMap E Ω) :
    let algPS : Algebra E (PowerSeries Ω) := τ.toAlgebra
    -- The tensor product uses the deformed action, not coefficientwise scalar multiplication.
    let _ : Module E (PowerSeries Ω) := algPS.toModule
    ∃ e : (PowerSeries Ω ⊗[E] F) ≃ₐ[PowerSeries Ω]
        ((F →ₐ[E] Ω) → PowerSeries Ω),
      ∀ (a : PowerSeries Ω) (b : F) (ι : F →ₐ[E] Ω),
        e (a ⊗ₜ[E] b) ι = a * formalEmbeddingLift τ hτ ι b := by
  classical
  intro algPS modPS
  let pb := Field.powerBasisOfFiniteOfSeparable E F
  let _ : Fintype (F →ₐ[E] Ω) := PowerBasis.AlgHom.fintype pb
  have hcard : Fintype.card (F →ₐ[E] Ω) = pb.dim :=
    AlgHom.card_of_powerBasis pb (Algebra.IsSeparable.isSeparable E pb.gen)
      (IsAlgClosed.splits _)
  let index : (F →ₐ[E] Ω) ≃ Fin pb.dim := Fintype.equivFinOfCardEq hcard
  let φ (ι : F →ₐ[E] Ω) : F →ₐ[E] PowerSeries Ω :=
    { toRingHom := formalEmbeddingLift τ hτ ι
      commutes' := fun a => RingHom.congr_fun (formalEmbeddingLift_spec τ hτ ι).1 a }
  let f : (PowerSeries Ω ⊗[E] F) →ₐ[PowerSeries Ω]
      ((F →ₐ[E] Ω) → PowerSeries Ω) :=
    AlgHom.pi fun ι => AlgHom.liftEquiv E (PowerSeries Ω) F (PowerSeries Ω) (φ ι)
  let fN : (PowerSeries Ω ⊗[E] F) →ₐ[PowerSeries Ω]
      (Fin pb.dim → PowerSeries Ω) :=
    AlgHom.pi fun i =>
      AlgHom.liftEquiv E (PowerSeries Ω) F (PowerSeries Ω) (φ (index.symm i))
  let b := pb.basis.baseChange (PowerSeries Ω)
  let c := Pi.basisFun (PowerSeries Ω) (Fin pb.dim)
  let M := LinearMap.toMatrix b c fN.toLinearMap
  have hmatrix : M = Matrix.vandermonde
      (fun i : Fin pb.dim => formalEmbeddingLift τ hτ (index.symm i) pb.gen) := by
    apply Matrix.ext
    intro i j
    change LinearMap.toMatrix b c fN.toLinearMap i j = _
    rw [LinearMap.toMatrix_apply]
    simp only [c, Pi.basisFun_repr]
    change fN ((pb.basis.baseChange (PowerSeries Ω)) j) i =
      (formalEmbeddingLift τ hτ (index.symm i) pb.gen) ^ (j : ℕ)
    rw [Module.Basis.baseChange_apply, PowerBasis.basis_eq_pow]
    change (AlgHom.liftEquiv E (PowerSeries Ω) F (PowerSeries Ω)
      (φ (index.symm i))) ((1 : PowerSeries Ω) ⊗ₜ[E] (pb.gen ^ (j : ℕ))) = _
    rw [AlgHom.liftEquiv_tmul, one_smul]
    exact (φ (index.symm i)).map_pow pb.gen (j : ℕ)
  have hresidue : M.map constantCoeff =
      Matrix.vandermonde (fun i : Fin pb.dim => index.symm i pb.gen) := by
    rw [hmatrix]
    apply Matrix.ext
    intro i j
    change constantCoeff ((formalEmbeddingLift τ hτ (index.symm i) pb.gen) ^ (j : ℕ)) =
      (index.symm i pb.gen) ^ (j : ℕ)
    rw [map_pow]
    exact congrArg (fun z : Ω => z ^ (j : ℕ))
      (RingHom.congr_fun (formalEmbeddingLift_spec τ hτ (index.symm i)).2 pb.gen)
  have hdet : IsUnit M.det := by
    apply isUnit_iff_constantCoeff.mpr
    apply isUnit_iff_ne_zero.mpr
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hresidue,
      Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    apply index.symm.injective
    exact pb.algHom_ext hij
  let eLin : (PowerSeries Ω ⊗[E] F) ≃ₗ[PowerSeries Ω]
      (Fin pb.dim → PowerSeries Ω) :=
    Matrix.toLinOfInv b c (Matrix.mul_nonsing_inv M hdet) (Matrix.nonsing_inv_mul M hdet)
  have hlin : eLin.toLinearMap = fN.toLinearMap := by
    change Matrix.toLin b c M = fN.toLinearMap
    exact Matrix.toLin_toMatrix b c fN.toLinearMap
  have hfN : Function.Bijective fN := by
    change Function.Bijective fN.toLinearMap
    rw [← hlin]
    exact eLin.bijective
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply hfN.injective
      funext i
      exact congrFun hab (index.symm i)
    · intro y
      obtain ⟨a, ha⟩ := hfN.surjective (fun i => y (index.symm i))
      refine ⟨a, ?_⟩
      funext ι
      have h := congrFun ha (index ι)
      change f a (index.symm (index ι)) = y (index.symm (index ι)) at h
      simpa only [Equiv.symm_apply_apply] using h
  refine ⟨AlgEquiv.ofBijective f hf, ?_⟩
  intro a b ι
  change (AlgHom.liftEquiv E (PowerSeries Ω) F (PowerSeries Ω) (φ ι))
    (a ⊗ₜ[E] b) = a * formalEmbeddingLift τ hτ ι b
  exact AlgHom.liftEquiv_tmul (φ ι) a b

end PowerSeries
