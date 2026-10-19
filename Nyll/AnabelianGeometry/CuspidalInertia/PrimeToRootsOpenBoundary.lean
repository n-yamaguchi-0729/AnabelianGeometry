/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.CuspidalInertia.BoundaryCoordinateOpenEquivariance
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsSurjectivity
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsCharacters
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsResidueAction
import Mathlib.FieldTheory.KrullTopology

/-!
# Open boundary equivariance for the actual roots limit

Use the actual third-root projection and its field-element stabilizer.
The finite-character argument then upgrades the original twisted boundary
formula to coordinatewise equivariance on an open Galois subgroup.
-/

noncomputable section

open ProCGroups.InverseSystems EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.CuspidalInertia

theorem exists_open_actual_roots_boundary_equivariance
    (K Ω : Type) [Field K] [Field Ω] [CharZero Ω] [IsAlgClosed Ω]
    [Algebra K Ω] [Algebra.IsIntegral K Ω]
    (S : Type) [Finite S] [DecidableEq S] (s0 : S)
    :
    let R := (primeToRootsSystem Ω Ω).inverseLimit
    let B := (S → R) ⧸ (Pi.constMonoidHom S R).range
    ∀ ρ : (Ω ≃ₐ[K] Ω) →* MulAut B,
      (∀ b, Continuous (fun σ : Ω ≃ₐ[K] Ω => ρ σ b)) →
      (∀ σ : Ω ≃ₐ[K] Ω, ∃ f : S → S, ∀ (p : S) (t : R),
        ρ σ (QuotientGroup.mk (fun s : S => if s = p then t else 1)) =
          QuotientGroup.mk (fun s : S => if s = f p then
            primeToRootsCoefficientMap Ω Ω σ.toRingHom t else 1)) →
      ∃ U : OpenSubgroup (Ω ≃ₐ[K] Ω), ∀ σ ∈ U, ∀ (p : S) (t : R),
        ρ σ (QuotientGroup.mk (fun s : S => if s = p then t else 1)) =
          QuotientGroup.mk (fun s : S => if s = p then
            primeToRootsCoefficientMap Ω Ω σ.toRingHom t else 1) := by
  intro R B ρ hρ hperm
  classical
  let n : InvertibleExponent Ω := ⟨3, isUnit_iff_ne_zero.mpr (by norm_num)⟩
  let : TopologicalSpace (rootsOfUnity 3 Ω) := ⊥
  have : DiscreteTopology (rootsOfUnity 3 Ω) := ⟨rfl⟩
  let π : (primeToRootsSystem Ω Ω).inverseLimit →* rootsOfUnity 3 Ω :=
    projectionHom (primeToRootsSystem Ω Ω) n
  have hπ : Continuous π := (primeToRootsSystem Ω Ω).continuous_projection n
  have hH (z : rootsOfUnity 3 Ω) : z ^ 3 = 1 := by
    apply Subtype.ext
    exact (mem_rootsOfUnity 3 (z : Ωˣ)).mp z.property
  have hker (r : (primeToRootsSystem Ω Ω).inverseLimit) :
      π r = 1 ↔ ∃ y, y ^ 3 = r := by
    constructor
    · exact primeToRoots_exists_pow_eq_of_projection_eq_one n r
    · rintro ⟨y, rfl⟩
      rw [map_pow]
      exact hH _
  obtain ⟨η, _, _, hη⟩ := exists_third_root_ne_one Ω
  obtain ⟨t0, ht0⟩ := primeToRoots_projection_surjective Ω Ω n η
  have ht : (π t0) ^ 2 ≠ 1 := by
    change π t0 = η at ht0
    rw [ht0]
    exact hη
  let ζ : Ω := ((π t0 : Ωˣ) : Ω)
  let V : OpenSubgroup (Ω ≃ₐ[K] Ω) :=
    ⟨MulAction.stabilizer (Ω ≃ₐ[K] Ω) ζ,
      stabilizer_isOpen_of_isIntegral (K := K) (L := Ω) ζ⟩
  have hV : ∀ σ ∈ V,
      π (primeToRootsCoefficientMap Ω Ω σ.toRingHom t0) = π t0 := by
    intro σ hσ
    have hfix : σ ζ = ζ := by
      change σ ζ = ζ at hσ
      exact hσ
    apply rootsOfUnity.coe_injective
    exact (primeToRootsCoefficientMap_scalar Ω Ω σ.toRingHom n t0).trans hfix
  exact exists_open_boundary_coordinate_equivariance
    (Γ := Ω ≃ₐ[K] Ω) (R := (primeToRootsSystem Ω Ω).inverseLimit)
    (H := rootsOfUnity 3 Ω) (S := S) s0 π hπ 3 hker hH t0 ht
    (fun σ => primeToRootsCoefficientMap Ω Ω σ.toRingHom) V hV ρ hρ hperm

/-- The same result applies to the original quotient when its kernel is
identified with the diagonal; no transport of the surrounding sequence is needed. -/
theorem exists_open_actual_roots_boundary_equivariance_of_diagonal_relation
    (K Ω : Type) [Field K] [Field Ω] [CharZero Ω] [IsAlgClosed Ω]
    [Algebra K Ω] [Algebra.IsIntegral K Ω]
    (S : Type) [Finite S] [DecidableEq S] (s0 : S)
    (N : Subgroup (S → (primeToRootsSystem Ω Ω).inverseLimit))
    (hN : N = (Pi.constMonoidHom S (primeToRootsSystem Ω Ω).inverseLimit).range)
    (ρ : (Ω ≃ₐ[K] Ω) →*
      MulAut ((S → (primeToRootsSystem Ω Ω).inverseLimit) ⧸ N))
    (hρ : ∀ b, Continuous (fun σ : Ω ≃ₐ[K] Ω => ρ σ b))
    (hperm : ∀ σ : Ω ≃ₐ[K] Ω, ∃ f : S → S, ∀ (p : S)
        (t : (primeToRootsSystem Ω Ω).inverseLimit),
      ρ σ (QuotientGroup.mk (fun s : S => if s = p then t else 1)) =
        QuotientGroup.mk (fun s : S => if s = f p then
          primeToRootsCoefficientMap Ω Ω σ.toRingHom t else 1)) :
    ∃ U : OpenSubgroup (Ω ≃ₐ[K] Ω), ∀ σ ∈ U, ∀ (p : S)
        (t : (primeToRootsSystem Ω Ω).inverseLimit),
      ρ σ (QuotientGroup.mk (fun s : S => if s = p then t else 1)) =
        QuotientGroup.mk (fun s : S => if s = p then
          primeToRootsCoefficientMap Ω Ω σ.toRingHom t else 1) := by
  subst N
  exact exists_open_actual_roots_boundary_equivariance K Ω S s0 ρ hρ hperm

end AnabelianGeometry.CuspidalInertia
