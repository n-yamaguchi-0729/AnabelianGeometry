/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.FiniteAlgebraHom
import Mathlib.FieldTheory.Finite.Basic

/-!
# Finiteness of actual Frobenius-fixed affine coordinates

The fixed values lie in the finite root set of `X^q - X`. Corestricting
algebra maps to this equalizer reuses finite-type algebra-map finiteness.
No dimension-zero hypothesis or finiteness at individual torsion levels is used.
-/

namespace AnabelianGeometry.WeightFiltration

/-- Fixed algebra maps from a finite-type algebra factor through the finite
fixed-value subalgebra, over an arbitrary commutative base ring. -/
theorem finite_fixed_algHom
    (R A Ω : Type*) [CommRing R] [CommRing A] [CommRing Ω]
    [Algebra R A] [Algebra R Ω] [Algebra.FiniteType R A]
    (σ : Ω ≃ₐ[R] Ω) [Finite {x : Ω // σ x = x}] :
    Finite {f : A →ₐ[R] Ω // ∀ a, σ (f a) = f a} := by
  let S := AlgHom.equalizer σ.toAlgHom (AlgHom.id R Ω)
  have : Finite S := inferInstanceAs (Finite {x : Ω // σ x = x})
  have : Finite (A →ₐ[R] S) := finite_algHom_of_finiteType R A S
  let restrict (f : {f : A →ₐ[R] Ω // ∀ a, σ (f a) = f a}) : A →ₐ[R] S :=
    f.val.codRestrict S (fun a => f.property a)
  apply Finite.of_injective restrict
  intro f g h
  apply Subtype.ext
  ext a
  exact congrArg (fun ψ : A →ₐ[R] S => (ψ a : Ω)) h

/-- Frobenius has finitely many fixed values, by the polynomial `X^q - X`. -/
theorem finite_frobenius_fixed_values
    (k Ω : Type*) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] :
    Finite {x : Ω // FiniteField.frobeniusAlgEquivOfAlgebraic k Ω x = x} := by
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k Ω
  have hσ (x : Ω) : σ x = x ^ Fintype.card k :=
    congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic k Ω) x
  have hS : {x : Ω | σ x = x} =
      {x | Polynomial.IsRoot (Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial Ω) x} := by
    ext x
    change (σ x = x) ↔ _
    rw [hσ]
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, sub_eq_zero, Set.mem_ofPred_eq]
  have hfinite : Set.Finite {x : Ω | σ x = x} := by
    rw [hS]
    exact Polynomial.finite_setOfPred_isRoot
      (FiniteField.X_pow_card_sub_X_ne_zero Ω Fintype.one_lt_card)
  exact hfinite.to_subtype

/-- Frobenius-fixed algebra maps from a finite-type algebra form a finite type. -/
theorem finite_frobenius_fixed_algHom
    (k A Ω : Type*) [Field k] [Fintype k] [CommRing A] [Field Ω]
    [Algebra k A] [Algebra k Ω] [Algebra.FiniteType k A]
    [Algebra.IsAlgebraic k Ω] :
    Finite {f : A →ₐ[k] Ω // ∀ a,
      FiniteField.frobeniusAlgEquivOfAlgebraic k Ω (f a) = f a} := by
  have := finite_frobenius_fixed_values k Ω
  exact finite_fixed_algHom k A Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)

end AnabelianGeometry.WeightFiltration
