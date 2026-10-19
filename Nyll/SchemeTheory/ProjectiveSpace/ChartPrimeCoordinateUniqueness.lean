/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Affine chart primes determined by their coordinate values -/

noncomputable section

namespace AlgebraicGeometry.ProjSpace

open MvPolynomial

universe u v w

variable {K : Type u} [Field K]
variable {A : Type v} [CommRing A] [Algebra K A]
variable {ι : Type w}

/-- A prime containing all coordinate-minus-value relations is the evaluation kernel. -/
theorem prime_eq_ker_coordinateEvaluation
    (e : MvPolynomial ι K ≃ₐ[K] A) (p : Ideal A) [p.IsPrime]
    (t : ι → K) (ht : ∀ i, e (X i) - algebraMap K A (t i) ∈ p) :
    p = RingHom.ker (((MvPolynomial.aeval t).comp e.symm.toAlgHom).toRingHom) := by
  let q : A →ₐ[K] A ⧸ p := Ideal.Quotient.mkₐ K p
  have hq : q.comp e.toAlgHom =
      (Algebra.ofId K (A ⧸ p)).comp (MvPolynomial.aeval t) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    change q (e (X i)) = algebraMap K (A ⧸ p) (t i)
    rw [← q.commutes (t i)]
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (ht i)
  have hvalue (x : A) : Ideal.Quotient.mk p x =
      algebraMap K (A ⧸ p) (MvPolynomial.aeval t (e.symm x)) := by
    have h := DFunLike.congr_fun hq (e.symm x)
    change q x = _
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply, Algebra.ofId_apply] using h
  ext x
  change x ∈ p ↔ MvPolynomial.aeval t (e.symm x) = 0
  rw [← Ideal.Quotient.eq_zero_iff_mem, hvalue]
  constructor
  · intro h
    apply (algebraMap K (A ⧸ p)).injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

/-- Equal coordinate values determine the same actual affine prime. -/
theorem prime_eq_of_coordinateValues
    (e : MvPolynomial ι K ≃ₐ[K] A) (p q : Ideal A) [p.IsPrime] [q.IsPrime]
    (t : ι → K)
    (hp : ∀ i, e (X i) - algebraMap K A (t i) ∈ p)
    (hq : ∀ i, e (X i) - algebraMap K A (t i) ∈ q) : p = q :=
  (prime_eq_ker_coordinateEvaluation e p t hp).trans
    (prime_eq_ker_coordinateEvaluation e q t hq).symm

end AlgebraicGeometry.ProjSpace
