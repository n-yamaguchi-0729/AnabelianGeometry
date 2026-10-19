/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
import Nyll.ProCGroups.InverseSystems.CofinalityAndDensity
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# A common roots index in characteristic zero

Changing the characteristic-zero field used to index invertible exponents
preserves every exponent and every roots coordinate. The existing cofinal
reindexing homeomorphism supplies the inverse-limit comparison.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open ProCGroups.InverseSystems

universe u v w

/-- Characteristic-zero exponent indices agree by their literal positive integer values. -/
def InvertibleExponent.charZeroOrderIso
    (k : Type u) (l : Type v) [Field k] [Field l] [CharZero k] [CharZero l] :
    InvertibleExponent k ≃o InvertibleExponent l where
  toFun n := ⟨n.val, isUnit_iff_ne_zero.mpr
    (Nat.cast_ne_zero.mpr (InvertibleExponent.pos k n).ne')⟩
  invFun n := ⟨n.val, isUnit_iff_ne_zero.mpr
    (Nat.cast_ne_zero.mpr (InvertibleExponent.pos l n).ne')⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

/-- Changing the characteristic-zero index field leaves the full roots limit unchanged. -/
def primeToRootsCharZeroIndexEquiv
    (k : Type u) (l : Type v) (E : Type w)
    [Field k] [Field l] [Field E] [CharZero k] [CharZero l] :
    (primeToRootsSystem k E).inverseLimit ≃ₜ* (primeToRootsSystem l E).inverseLimit := by
  let σ := InvertibleExponent.charZeroOrderIso l k
  have hcofinal : ∀ i : InvertibleExponent k, ∃ n : InvertibleExponent l, i ≤ σ n :=
    fun i => ⟨σ.symm i, by rw [σ.apply_symm_apply]⟩
  let e : (primeToRootsSystem k E).inverseLimit ≃ₜ
      (primeToRootsSystem l E).inverseLimit :=
    (primeToRootsSystem k E).homeomorph_reindex_cofinal σ σ.monotone
      (InvertibleExponent.directed l) hcofinal
  exact ContinuousMulEquiv.mk' e (by
    intro x y
    apply (primeToRootsSystem l E).ext
    intro n
    rfl)

/-- Reindexing retains the original root at the same positive integer exponent. -/
theorem primeToRootsCharZeroIndexEquiv_projection
    (k : Type u) (l : Type v) (E : Type w)
    [Field k] [Field l] [Field E] [CharZero k] [CharZero l]
    (x : (primeToRootsSystem k E).inverseLimit) (n : InvertibleExponent l) :
    (primeToRootsSystem l E).projection n (primeToRootsCharZeroIndexEquiv k l E x) =
      (primeToRootsSystem k E).projection (InvertibleExponent.charZeroOrderIso l k n) x := rfl

end EtaleFundamentalGroups.Inertia
