/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Nondegeneracy after an injective extension of scalars

The Gram matrix in the extended basis is the original Gram matrix with
its entries mapped to the new ring. Over domains its determinant therefore
remains nonzero under an injective coefficient map.
-/

@[expose] public section

noncomputable section

namespace LinearMap.BilinForm

variable {R A M ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

/-- The actual Gram matrix after scalar extension is obtained by
applying the coefficient map to the original entries. -/
theorem toMatrix_baseChange (b : Module.Basis ι R M) (B : LinearMap.BilinForm R M) :
    toMatrix (b.baseChange A) (B.baseChange A) =
      (toMatrix b B).map (algebraMap R A) := by
  ext i j
  simp only [Matrix.map_apply, toMatrix_apply, Module.Basis.baseChange_apply,
    baseChange_tmul, mul_one, Algebra.algebraMap_eq_smul_one]

omit [Fintype ι] [DecidableEq ι] in
/-- Nondegeneracy of a finite free bilinear form survives an
injective extension of its domain of coefficients. -/
theorem Nondegenerate.baseChange_of_injective [Finite ι] [IsDomain R] [IsDomain A]
    {B : LinearMap.BilinForm R M} (hB : B.Nondegenerate) (b : Module.Basis ι R M)
    (hinj : Function.Injective (algebraMap R A)) :
    (B.baseChange A).Nondegenerate := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  apply nondegenerate_of_det_ne_zero (B.baseChange A) (b.baseChange A)
  rw [toMatrix_baseChange]
  change ((algebraMap R A).mapMatrix (LinearMap.BilinForm.toMatrix b B)).det ≠ 0
  rw [← RingHom.map_det]
  intro h
  apply (nondegenerate_iff_det_ne_zero b).mp hB
  apply hinj
  exact h.trans (map_zero (algebraMap R A)).symm

end LinearMap.BilinForm
