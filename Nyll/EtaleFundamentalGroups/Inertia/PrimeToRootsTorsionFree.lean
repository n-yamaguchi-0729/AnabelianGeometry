/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem

/-!
# Integer torsion in the actual roots inverse limit

A power invertible in the index field is injective, as is seen at the
coordinate multiplied by that power. In characteristic zero this applies
to every nonzero integer exponent, without a choice of roots generator.
-/

namespace EtaleFundamentalGroups.Inertia

open ProCGroups.InverseSystems

/-- An invertible exponent acts injectively on the full roots inverse limit. -/
theorem primeToRoots_pow_injective
    (k E : Type*) [Field k] [Field E] (n : InvertibleExponent k) :
    Function.Injective (fun x : (primeToRootsSystem k E).inverseLimit => x ^ n.val) := by
  intro x y hxy
  apply (primeToRootsSystem k E).ext
  intro m
  let mn : InvertibleExponent k := ⟨m.val * n.val, by
    rw [Nat.cast_mul]
    exact m.property.mul n.property⟩
  let zx (r : InvertibleExponent k) : rootsOfUnity r.val E := x.val r
  let zy (r : InvertibleExponent k) : rootsOfUnity r.val E := y.val r
  have hx := congrArg (fun z : rootsOfUnity m.val E => (z : Eˣ))
    (x.property m mn (dvd_mul_right m.val n.val))
  have hy := congrArg (fun z : rootsOfUnity m.val E => (z : Eˣ))
    (y.property m mn (dvd_mul_right m.val n.val))
  change (zx mn : Eˣ) ^ (m.val * n.val / m.val) = (zx m : Eˣ) at hx
  change (zy mn : Eˣ) ^ (m.val * n.val / m.val) = (zy m : Eˣ) at hy
  rw [Nat.mul_div_cancel_left _ (InvertibleExponent.pos k m)] at hx hy
  have hp := congrArg (projectionHom (primeToRootsSystem k E) mn) hxy
  rw [map_pow, map_pow] at hp
  have hp' := congrArg (fun z : rootsOfUnity mn.val E => (z : Eˣ)) hp
  apply Subtype.ext
  exact hx.symm.trans (hp'.trans hy)

/-- In characteristic zero a nontrivial roots parameter stays nontrivial
after every positive integer power. -/
theorem primeToRoots_pow_ne_one
    (k E : Type*) [Field k] [Field E] [CharZero k]
    {x : (primeToRootsSystem k E).inverseLimit} (hx : x ≠ 1)
    {n : ℕ} (hn : n ≠ 0) : x ^ n ≠ 1 := by
  let m : InvertibleExponent k :=
    ⟨n, isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)⟩
  intro h
  apply hx
  apply primeToRoots_pow_injective k E m
  exact h.trans (one_pow n).symm

end EtaleFundamentalGroups.Inertia
