/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsResidueAction
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsSurjectivity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Perfect

/-! # Characteristic and Frobenius in the actual roots representation

The characteristic is the unique prime whose power map on the complete
prime-to-characteristic roots inverse limit is surjective. Over a finite field,
the action of its actual algebraic-closure Galois group on this limit is faithful,
and arithmetic Frobenius is the unique automorphism acting by the field-cardinality
power. The proofs use finite subfields and actual roots coordinates.

These are coefficient-level inputs to finite-field reconstruction. No
identification of a curve's determinant representation with a cyclotomic power,
or recovery of its geometric subgroup from an unmarked arithmetic group, is
asserted here. In particular these statements do not replace the geometric
parts of Yamaguchi, arXiv:2302.09253, Lemmas 1.4 and 1.8.
-/

noncomputable section
open EtaleFundamentalGroups.Inertia ProCGroups.InverseSystems

namespace AnabelianGeometry.WeightFiltration

private theorem primeToRoots_projection_scalar_pow
    (k E : Type*) [Field k] [Field E]
    (n : InvertibleExponent k) (t : (primeToRootsSystem k E).inverseLimit) (m : ℕ) :
    ((primeToRootsSystem k E).projection n (t ^ m)).val.val =
      ((primeToRootsSystem k E).projection n t).val.val ^ m := by
  calc
    ((primeToRootsSystem k E).projection n (t ^ m)).val.val =
        (((primeToRootsSystem k E).projection n t) ^ m).val.val :=
      congrArg (fun ζ : rootsOfUnity n.val E => ζ.val.val)
        (map_pow (projectionHom (S := primeToRootsSystem k E) n) t m)
    _ = ((primeToRootsSystem k E).projection n t).val.val ^ m :=
      rootsOfUnity.coe_pow _ m

section Characteristic

variable (k E : Type*) [Field k] [Field E] [Algebra k E] [IsAlgClosed E]
    (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The characteristic power is bijective on the actual prime-to-characteristic
roots limit, because it is induced by the coefficient Frobenius automorphism. -/
theorem primeToRoots_characteristic_pow_bijective :
    Function.Bijective (fun t : (primeToRootsSystem k E).inverseLimit => t ^ p) := by
  let : CharP E p := charP_of_injective_algebraMap' k p
  let e := primeToRootsResidueEquiv k E (frobeniusEquiv E p)
  have he : (fun t => e t) = (fun t : (primeToRootsSystem k E).inverseLimit => t ^ p) := by
    funext t
    apply (primeToRootsSystem k E).ext
    intro n
    apply rootsOfUnity.coe_injective
    change ((primeToRootsSystem k E).projection n
      (primeToRootsCoefficientMap k E (frobeniusEquiv E p).toRingHom t)).val.val =
        ((primeToRootsSystem k E).projection n (t ^ p)).val.val
    rw [primeToRootsCoefficientMap_scalar, primeToRoots_projection_scalar_pow]
    exact frobeniusEquiv_def E p (((primeToRootsSystem k E).projection n t).val.val)
  rw [← he]
  exact e.bijective

/-- Surjectivity of a prime power map on the actual roots group singles out
the characteristic. This is an invariant of the group alone. -/
theorem primeToRoots_prime_pow_surjective_iff
    (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Function.Surjective (fun t : (primeToRootsSystem k E).inverseLimit => t ^ ℓ) ↔ ℓ = p := by
  constructor
  · intro hsurj
    by_contra hne
    have hℓk : (ℓ : k) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime k hℓ (Ne.symm hne)
    have hℓE : (ℓ : E) ≠ 0 := by
      intro h
      apply hℓk
      apply (algebraMap k E).injective
      simpa only [map_natCast, map_zero] using h
    let : NeZero (ℓ : E) := ⟨hℓE⟩
    let : NeZero ℓ := ⟨hℓ.ne_zero⟩
    let n : InvertibleExponent k := ⟨ℓ, isUnit_iff_ne_zero.mpr hℓk⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot E ℓ
    let η : rootsOfUnity n.val E := hζ.toRootsOfUnity
    obtain ⟨t, ht⟩ := primeToRoots_projection_surjective k E n η
    obtain ⟨u, hu⟩ := hsurj t
    have hscalar := congrArg
      (fun v : (primeToRootsSystem k E).inverseLimit =>
        ((primeToRootsSystem k E).projection n v).val.val) hu
    rw [primeToRoots_projection_scalar_pow] at hscalar
    rw [ht] at hscalar
    have hroot : (((primeToRootsSystem k E).projection n u).val.val) ^ ℓ = 1 :=
      (mem_rootsOfUnity' ℓ ((primeToRootsSystem k E).projection n u).val).mp
        ((primeToRootsSystem k E).projection n u).property
    exact hζ.ne_one hℓ.one_lt (hscalar.symm.trans hroot)
  · intro h
    subst ℓ
    exact (primeToRoots_characteristic_pow_bijective k E p).2

/-- An abstract group isomorphism between these complete roots limits preserves
positive characteristic; no chosen generator or coefficient compatibility is needed. -/
theorem primeToRoots_characteristic_eq_of_mulEquiv
    (k' E' : Type*) [Field k'] [Field E'] [Algebra k' E'] [IsAlgClosed E']
    (p' : ℕ) [Fact p'.Prime] [CharP k' p']
    (e : (primeToRootsSystem k E).inverseLimit ≃*
      (primeToRootsSystem k' E').inverseLimit) : p = p' := by
  apply (primeToRoots_prime_pow_surjective_iff k' E' p' p (Fact.out : p.Prime)).mp
  intro y
  obtain ⟨x, hx⟩ := (primeToRoots_characteristic_pow_bijective k E p).2 (e.symm y)
  refine ⟨e x, ?_⟩
  exact (map_pow e x p).symm.trans
    ((congrArg e hx).trans (e.apply_symm_apply y))

end Characteristic

section FiniteField

variable (k E : Type*) [Field k] [Finite k] [Field E] [Algebra k E]
    [Algebra.IsAlgebraic k E] [IsAlgClosed E]

omit [IsAlgClosed E] in
/-- A nonzero algebraic element over a finite field belongs to an actual
finite roots coordinate whose exponent is invertible in the base field. -/
private theorem finiteField_nonzero_root_coordinate (x : E) (hx : x ≠ 0) :
    ∃ (n : InvertibleExponent k) (ζ : rootsOfUnity n.val E), ζ.val.val = x := by
  let F := IntermediateField.adjoin k ({x} : Set E)
  let : FiniteDimensional k F :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := k) x)
  let : Finite F := Module.finite_of_finite k
  let : Fintype F := Fintype.ofFinite F
  let xF : F := ⟨x, IntermediateField.subset_adjoin k ({x} : Set E) (Set.mem_singleton x)⟩
  have hxF : xF ≠ 0 := by
    intro h
    exact hx (congrArg (fun y : F => (y : E)) h)
  let n₀ := Fintype.card F - 1
  have hnF : (n₀ : F) = -1 := by
    change ((Fintype.card F - 1 : ℕ) : F) = -1
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero)),
      FiniteField.cast_card_eq_zero, Nat.cast_one, zero_sub]
  have hnk : (n₀ : k) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap k F) h
    have hnF0 : (n₀ : F) = 0 := by
      simpa only [map_natCast, map_zero] using h'
    exact (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)) (hnF.symm.trans hnF0)
  let n : InvertibleExponent k := ⟨n₀, isUnit_iff_ne_zero.mpr hnk⟩
  let : NeZero n.val := ⟨(InvertibleExponent.pos k n).ne'⟩
  have hpow : x ^ n.val = 1 := by
    have h := congrArg (fun y : F => (y : E)) (FiniteField.pow_card_sub_one_eq_one xF hxF)
    exact h
  exact ⟨n, rootsOfUnity.mkOfPowEq x hpow, rfl⟩

/-- The actual Galois action on the full prime-to-characteristic roots limit
is faithful over a finite field. -/
theorem finiteField_primeToRootsAction_injective :
    Function.Injective (fun σ : E ≃ₐ[k] E =>
      primeToRootsResidueEquiv k E σ.toRingEquiv) := by
  intro σ τ h
  apply AlgEquiv.ext
  intro x
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero]
  · obtain ⟨n, ζ, hζ⟩ := finiteField_nonzero_root_coordinate k E x hx
    obtain ⟨t, ht⟩ := primeToRoots_projection_surjective k E n ζ
    have hcoord := congrArg
      (fun e : Equiv.Perm (primeToRootsSystem k E).inverseLimit =>
        ((primeToRootsSystem k E).projection n (e t)).val.val) h
    change σ (((primeToRootsSystem k E).projection n t).val.val) =
      τ (((primeToRootsSystem k E).projection n t).val.val) at hcoord
    rw [ht, hζ] at hcoord
    exact hcoord

omit [Finite k] [IsAlgClosed E] in
/-- Arithmetic Frobenius acts on every actual roots coordinate by the
cardinality power, hence by that power on the entire inverse limit. -/
theorem finiteField_frobenius_primeToRoots [Fintype k]
    (t : (primeToRootsSystem k E).inverseLimit) :
    primeToRootsCoefficientMap k E
      (FiniteField.frobeniusAlgEquivOfAlgebraic k E).toRingHom t =
        t ^ Fintype.card k := by
  apply (primeToRootsSystem k E).ext
  intro n
  apply rootsOfUnity.coe_injective
  change ((primeToRootsSystem k E).projection n
    (primeToRootsCoefficientMap k E
      (FiniteField.frobeniusAlgEquivOfAlgebraic k E).toRingHom t)).val.val =
    ((primeToRootsSystem k E).projection n (t ^ Fintype.card k)).val.val
  exact (primeToRootsCoefficientMap_scalar k E _ n t).trans
    (primeToRoots_projection_scalar_pow k E n t (Fintype.card k)).symm

/-- Once the actual cyclotomic action and the field cardinality are known,
there is exactly one Galois element with the arithmetic-Frobenius action. -/
theorem finiteField_eq_frobenius_iff_primeToRoots [Fintype k]
    (σ : E ≃ₐ[k] E) :
    σ = FiniteField.frobeniusAlgEquivOfAlgebraic k E ↔
      ∀ t : (primeToRootsSystem k E).inverseLimit,
        primeToRootsCoefficientMap k E σ.toRingHom t = t ^ Fintype.card k := by
  constructor
  · intro h
    subst σ
    exact finiteField_frobenius_primeToRoots k E
  · intro h
    apply finiteField_primeToRootsAction_injective k E
    apply Equiv.ext
    intro t
    exact (h t).trans (finiteField_frobenius_primeToRoots k E t).symm

end FiniteField
end AnabelianGeometry.WeightFiltration
