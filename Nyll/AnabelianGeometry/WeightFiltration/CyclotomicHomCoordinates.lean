/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsCharacters
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsResidueAction
import Nyll.ProCGroups.Abelian.FullTateRestriction

/-!
# Scalar coordinates of actual cyclotomic homomorphisms

Equivariance and the roots action at a single exponent give the scalar
identity at that torsion coordinate. No scalar action on the full roots
source, projection surjectivity, or continuity hypothesis is used.
-/

namespace AnabelianGeometry.WeightFiltration

open EtaleFundamentalGroups.Inertia ProCGroups

variable {k E M : Type*} [Field k] [Field E] [AddCommGroup M]

/-- The actual finite torsion coordinate of a homomorphism from the roots limit. -/
def cyclotomicTorsionCoordinate
    (φ : (primeToRootsSystem k E).inverseLimit →* Multiplicative (FullTateModule M))
    (n : ℕ+) :
    (primeToRootsSystem k E).inverseLimit →* Multiplicative (torsionLevel M n) where
  toFun t := Multiplicative.ofAdd (FullTateModule.projection M n (Multiplicative.toAdd (φ t)))
  map_one' := by
    change FullTateModule.projection M n (Multiplicative.toAdd (φ 1)) = 0
    rw [map_one]
    exact (FullTateModule.projection M n).map_zero
  map_mul' x y := by
    change FullTateModule.projection M n (Multiplicative.toAdd (φ (x * y))) =
      FullTateModule.projection M n (Multiplicative.toAdd (φ x)) +
        FullTateModule.projection M n (Multiplicative.toAdd (φ y))
    rw [map_mul]
    exact (FullTateModule.projection M n).map_add _ _

/-- A roots-power identity at n and actual equivariance force the q-scalar
identity only at the corresponding finite torsion coordinate. -/
theorem cyclotomicHom_scalar_coordinate
    (φ : (primeToRootsSystem k E).inverseLimit →* Multiplicative (FullTateModule M))
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : k))
    (σ : (primeToRootsSystem k E).inverseLimit → (primeToRootsSystem k E).inverseLimit)
    (F : M →+ M) (q : ℕ) (t : (primeToRootsSystem k E).inverseLimit)
    (hroot : (((primeToRootsSystem k E).projection
        (⟨(n : ℕ), hn⟩ : InvertibleExponent k) (σ t)).val : E) =
      (((primeToRootsSystem k E).projection
        (⟨(n : ℕ), hn⟩ : InvertibleExponent k) t).val : E) ^ q)
    (heq : FullTateModule.evaluation M n (Multiplicative.toAdd (φ (σ t))) =
      F (FullTateModule.evaluation M n (Multiplicative.toAdd (φ t)))) :
    F (FullTateModule.evaluation M n (Multiplicative.toAdd (φ t))) =
      q • FullTateModule.evaluation M n (Multiplicative.toAdd (φ t)) := by
  have hkill (a : Multiplicative (torsionLevel M n)) : a ^ (n : ℕ) = 1 := by
    change (n : ℕ) • Multiplicative.toAdd a = 0
    apply Subtype.ext
    exact (Multiplicative.toAdd a).property
  have h := primeToRoots_character_scalar_of_projection
    ⟨(n : ℕ), hn⟩ (cyclotomicTorsionCoordinate φ n) hkill σ q t (by
      apply rootsOfUnity.coe_injective
      exact hroot)
  have hval := congrArg
    (fun a : Multiplicative (torsionLevel M n) => (Multiplicative.toAdd a).val) h
  exact heq.symm.trans hval

/-- The actual coefficient action and an actual root-power formula supply
the coordinate hypothesis; no roots-limit action is supplied separately. -/
theorem cyclotomicHom_coefficient_scalar_coordinate
    (φ : (primeToRootsSystem k E).inverseLimit →* Multiplicative (FullTateModule M))
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : k))
    (σ : E →+* E) (F : M →+ M) (q : ℕ)
    (hroot : ∀ z : E, z ^ (n : ℕ) = 1 → σ z = z ^ q)
    (heq : ∀ t, φ (primeToRootsCoefficientMap k E σ t) =
      Multiplicative.ofAdd (FullTateModule.map F (Multiplicative.toAdd (φ t))))
    (t : (primeToRootsSystem k E).inverseLimit) :
    F (FullTateModule.evaluation M n (Multiplicative.toAdd (φ t))) =
      q • FullTateModule.evaluation M n (Multiplicative.toAdd (φ t)) := by
  apply cyclotomicHom_scalar_coordinate φ n hn
    (primeToRootsCoefficientMap k E σ) F q t
  · let z : rootsOfUnity (n : ℕ) E :=
      (primeToRootsSystem k E).projection (⟨(n : ℕ), hn⟩ : InvertibleExponent k) t
    change σ (z.val : E) = (z.val : E) ^ q
    apply hroot
    exact congrArg (fun u : Eˣ => (u : E))
      ((mem_rootsOfUnity (n : ℕ) z.val).mp z.property)
  · exact congrArg
      (fun y : Multiplicative (FullTateModule M) =>
        FullTateModule.evaluation M n (Multiplicative.toAdd y)) (heq t)

end AnabelianGeometry.WeightFiltration
