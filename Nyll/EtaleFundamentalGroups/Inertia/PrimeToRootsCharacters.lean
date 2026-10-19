/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem

/-!
# Finite-exponent characters of the actual roots inverse limit

The kernel of the n-th coordinate consists of n-th powers. Consequently a
character with exponent n depends only on that coordinate. This does not
assert that a local Frobenius is scalar on the full roots inverse limit.
-/

namespace EtaleFundamentalGroups.Inertia

open ProCGroups.InverseSystems

variable {k E : Type*} [Field k] [Field E]

/-- Division in the kernel of a roots coordinate is the literal shift to
the indices multiplied by that exponent. -/
theorem primeToRoots_exists_pow_eq_of_projection_eq_one
    (n : InvertibleExponent k) (x : (primeToRootsSystem k E).inverseLimit)
    (hx : (primeToRootsSystem k E).projection n x = 1) :
    ∃ y : (primeToRootsSystem k E).inverseLimit, y ^ n.val = x := by
  let mn (m : InvertibleExponent k) : InvertibleExponent k :=
    ⟨m.val * n.val, by
      rw [Nat.cast_mul]
      exact m.property.mul n.property⟩
  let z (m : InvertibleExponent k) : rootsOfUnity m.val E := x.val m
  have hroot (m : InvertibleExponent k) :
      (z (mn m) : Eˣ) ^ m.val = 1 := by
    have h := congrArg (fun z : rootsOfUnity n.val E => (z : Eˣ))
      (x.property n (mn m) (dvd_mul_left n.val m.val))
    change (z (mn m) : Eˣ) ^ (m.val * n.val / n.val) = (z n : Eˣ) at h
    rw [Nat.mul_div_cancel _ (InvertibleExponent.pos k n)] at h
    exact h.trans (congrArg (fun z : rootsOfUnity n.val E => (z : Eˣ)) hx)
  let y : (primeToRootsSystem k E).inverseLimit :=
    ⟨fun m => ⟨(z (mn m) : Eˣ), (mem_rootsOfUnity m.val _).mpr (hroot m)⟩, by
      intro m r hmr
      apply Subtype.ext
      have h := congrArg (fun z : rootsOfUnity (mn m).val E => (z : Eˣ))
        (x.property (mn m) (mn r) (Nat.mul_dvd_mul_right hmr n.val))
      change (z (mn r) : Eˣ) ^
        (r.val * n.val / (m.val * n.val)) = (z (mn m) : Eˣ) at h
      change (z (mn r) : Eˣ) ^ (r.val / m.val) = (z (mn m) : Eˣ)
      simpa only [Nat.mul_div_mul_right _ _ (InvertibleExponent.pos k n)] using h⟩
  refine ⟨y, ?_⟩
  apply (primeToRootsSystem k E).ext
  intro m
  change projectionHom (primeToRootsSystem k E) m (y ^ n.val) = _
  rw [map_pow]
  apply Subtype.ext
  have h := congrArg (fun z : rootsOfUnity m.val E => (z : Eˣ))
    (x.property m (mn m) (dvd_mul_right m.val n.val))
  change (z (mn m) : Eˣ) ^ (m.val * n.val / m.val) = (z m : Eˣ) at h
  change (z (mn m) : Eˣ) ^ n.val = (z m : Eˣ)
  simpa only [Nat.mul_div_cancel_left _ (InvertibleExponent.pos k m)] using h

/-- Finite-exponent characters agree on fibres of the actual roots projection. -/
theorem primeToRoots_character_eq_of_projection_eq
    {H : Type*} [Group H] (n : InvertibleExponent k)
    (φ : (primeToRootsSystem k E).inverseLimit →* H)
    (hH : ∀ a : H, a ^ n.val = 1)
    {x y : (primeToRootsSystem k E).inverseLimit}
    (hxy : (primeToRootsSystem k E).projection n x =
      (primeToRootsSystem k E).projection n y) : φ x = φ y := by
  have hz : (primeToRootsSystem k E).projection n (x * y⁻¹) = 1 := by
    rw [projection_mul (primeToRootsSystem k E),
      projection_inv (primeToRootsSystem k E), hxy, mul_inv_cancel]
  obtain ⟨z, hz⟩ := primeToRoots_exists_pow_eq_of_projection_eq_one n (x * y⁻¹) hz
  apply mul_inv_eq_one.mp
  rw [← map_inv, ← map_mul, ← hz, map_pow]
  exact hH (φ z)

/-- A scalar identity at the single relevant roots coordinate suffices for
every character killed by that exponent. -/
theorem primeToRoots_character_scalar_of_projection
    {H : Type*} [Group H] (n : InvertibleExponent k)
    (φ : (primeToRootsSystem k E).inverseLimit →* H)
    (hH : ∀ a : H, a ^ n.val = 1)
    (σ : (primeToRootsSystem k E).inverseLimit → (primeToRootsSystem k E).inverseLimit)
    (q : ℕ) (x : (primeToRootsSystem k E).inverseLimit)
    (hσ : (primeToRootsSystem k E).projection n (σ x) =
      ((primeToRootsSystem k E).projection n x) ^ q) :
    φ (σ x) = (φ x) ^ q := by
  have h : (primeToRootsSystem k E).projection n (σ x) =
      (primeToRootsSystem k E).projection n (x ^ q) :=
    hσ.trans ((projectionHom (primeToRootsSystem k E) n).map_pow x q).symm
  exact (primeToRoots_character_eq_of_projection_eq n φ hH h).trans (φ.map_pow x q)

end EtaleFundamentalGroups.Inertia
