/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Commutativity of the original Galois group over a finite field

Every element of the extension lies in an actual finite Galois intermediate
field. Restriction to that field makes the two original automorphisms commute,
because its finite-field Galois group is cyclic. This proves commutativity on
the original infinite group, so its literal comparison conjugations are trivial.
-/

@[expose] public section

namespace GaloisCohomology

/-- Any ring isomorphism between extensions of the same finite field
preserves that finite subfield, with a uniquely determined automorphism.
This follows by restriction over the prime field, without assuming scalar
linearity of the given map. -/
theorem exists_finiteBaseAutomorphism_of_ringEquiv
    (k : Type*) [Field k] [Finite k]
    {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra k F₁] [Algebra k F₂]
    (Φ : F₁ ≃+* F₂) :
    ∃ τ : k ≃+* k, ∀ z, Φ (algebraMap k F₁ z) = algebraMap k F₂ (τ z) := by
  let p := ringChar k
  let : Fact p.Prime := ⟨CharP.prime_ringChar k⟩
  let : Fintype k := Fintype.ofFinite k
  let : Algebra (ZMod p) k := ZMod.algebra k p
  let : Algebra (ZMod p) F₁ := ((algebraMap k F₁).comp (algebraMap (ZMod p) k)).toAlgebra
  let : Algebra (ZMod p) F₂ := ((algebraMap k F₂).comp (algebraMap (ZMod p) k)).toAlgebra
  have : IsScalarTower (ZMod p) k F₁ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (ZMod p) k F₂ := IsScalarTower.of_algebraMap_eq' rfl
  let e : F₁ ≃ₐ[ZMod p] F₂ :=
    { Φ with
      commutes' := by
        intro z
        exact RingHom.congr_fun
          (Subsingleton.elim (Φ.toRingHom.comp (algebraMap (ZMod p) F₁))
            (algebraMap (ZMod p) F₂)) z }
  refine ⟨(e.restrictNormal k).toRingEquiv, fun z => ?_⟩
  exact (e.restrictNormal_commutes k z).symm

variable (k κ : Type*) [Field k] [Finite k] [Field κ] [Algebra k κ] [IsGalois k κ]

/-- Automorphisms of the original Galois extension of a finite field commute. -/
theorem galois_mul_comm_of_finite_base (σ τ : Gal(κ/k)) : σ * τ = τ * σ := by
  apply AlgEquiv.ext
  intro x
  let L := FiniteGaloisIntermediateField.adjoin k ({x} : Set κ)
  have : Finite L := Module.finite_of_finite k
  let y : L := ⟨x, FiniteGaloisIntermediateField.subset_adjoin k {x} rfl⟩
  let r : Gal(κ/k) →* Gal(L/k) := AlgEquiv.restrictNormalHom L.toIntermediateField
  have hr : r (σ * τ) = r (τ * σ) :=
    (r.map_mul σ τ).trans ((mul_comm' (r σ) (r τ)).trans (r.map_mul τ σ).symm)
  have hvalue := congrArg (fun e : Gal(L/k) => algebraMap L κ (e y)) hr
  exact (AlgEquiv.restrictNormal_commutes (σ * τ) L y).symm.trans
    (hvalue.trans (AlgEquiv.restrictNormal_commutes (τ * σ) L y))

/-- A proposition-valued commutativity witness for the unchanged Galois group. -/
theorem galois_isMulCommutative_of_finite_base : IsMulCommutative Gal(κ/k) :=
  IsMulCommutative.of_comm (galois_mul_comm_of_finite_base k κ)

/-- Literal inner comparison conjugations over a finite constant field disappear. -/
theorem galois_conjugation_eq_of_finite_base (σ τ : Gal(κ/k)) : σ * τ * σ⁻¹ = τ := by
  rw [galois_mul_comm_of_finite_base k κ σ τ, mul_assoc, mul_inv_cancel, mul_one]

end GaloisCohomology
