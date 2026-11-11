/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.FieldTheory.FinitelyGeneratedModel
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finite residue fields of arithmetic models

A field finitely generated as an integer algebra is finite. Consequently,
every maximal residue field of an arithmetic affine model is finite.
-/

@[expose] public section

namespace FieldTheory

universe u

/-- A field finitely generated as a ring is finite. -/
theorem finite_of_finiteType_int
    (K : Type u) [Field K] [Algebra.FiniteType ℤ K] : Finite K := by
  have : IsJacobsonRing ℤ := int_isJacobsonRing
  have : Module.Finite ℤ K := finite_of_finite_type_of_isJacobsonRing ℤ K
  let p := ringChar K
  have hp : p ≠ 0 := ringChar_ne_zero_of_finiteType_int K
  have : NeZero p := ⟨hp⟩
  let : Algebra (ZMod p) K := ZMod.algebra K p
  have : Module.Finite (ZMod p) K :=
    Module.Finite.of_restrictScalars_finite ℤ (ZMod p) K
  exact Module.finite_of_finite (ZMod p)

/-- A closed point of a finite-type integer algebra has a finite residue field. -/
theorem finite_quotient_of_finiteType_int
    (A : Type u) [CommRing A] [Algebra.FiniteType ℤ A]
    (m : Ideal A) [m.IsMaximal] : Finite (A ⧸ m) := by
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  have hfin : Algebra.FiniteType ℤ (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mk m).toIntAlgHom
      Ideal.Quotient.mk_surjective
  exact @finite_of_finiteType_int (A ⧸ m) (Ideal.Quotient.field m) hfin

end FieldTheory
