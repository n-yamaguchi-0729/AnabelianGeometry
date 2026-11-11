/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Intrinsic subspaces from scalar-power differences

For an endomorphism `F` and scalar `a`, intersect the images of `F^n - a^n`
over positive integers. A finite-dimensional invariant subspace equals this
intersection if it has no `a^n` eigenvectors and one such difference maps the
ambient space into it. The construction is preserved by intertwining linear
equivalences.

This is purely linear algebra. Its intended cohomological application must
separately prove the proper-H¹ invariance, weight separation and finite boundary
permutation assertions for the actual curve and its actual Frobenius.
-/

@[expose] public section

noncomputable section

namespace LinearMap

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The original endomorphism minus the scalar at the same positive power. -/
def scalarPowerDifference (F : Module.End K V) (a : K) (n : ℕ+) : Module.End K V :=
  F ^ (n : ℕ) - a ^ (n : ℕ) • LinearMap.id

/-- An intrinsic subspace depending only on an endomorphism and a scalar. -/
def scalarPowerCore (F : Module.End K V) (a : K) : Submodule K V :=
  ⨅ n : ℕ+, LinearMap.range (scalarPowerDifference F a n)

/-- Powers preserve every invariant subspace of the original operator. -/
theorem pow_mem_of_invariant (F : Module.End K V) (S : Submodule K V)
    (hS : ∀ x ∈ S, F x ∈ S) (n : ℕ) {x : V} (hx : x ∈ S) : (F ^ n) x ∈ S := by
  induction n with
  | zero => simpa only [pow_zero, Module.End.one_apply] using hx
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hS _ ih

/-- On an invariant finite-dimensional subspace, absence of the scalar-power
eigenvalue makes each difference surjective on that same subspace. -/
theorem le_range_scalarPowerDifference_of_no_eigenvectors
    (F : Module.End K V) (a : K) (S : Submodule K V) [FiniteDimensional K S]
    (hS : ∀ x ∈ S, F x ∈ S) (n : ℕ+)
    (hno : ∀ x ∈ S, (F ^ (n : ℕ)) x = a ^ (n : ℕ) • x → x = 0) :
    S ≤ LinearMap.range (scalarPowerDifference F a n) := by
  let f := scalarPowerDifference F a n
  have hf : ∀ x ∈ S, f x ∈ S := by
    intro x hx
    exact S.sub_mem (pow_mem_of_invariant F S hS n hx) (S.smul_mem _ hx)
  have hi : Function.Injective (f.restrict hf) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply Subtype.ext
    apply hno x.val x.property
    have hz : f x.val = 0 := congrArg (fun z : S => (z : V)) hx
    exact sub_eq_zero.mp hz
  intro x hx
  obtain ⟨y, hy⟩ := LinearMap.surjective_of_injective hi (⟨x, hx⟩ : S)
  exact ⟨y.val, congrArg (fun z : S => (z : V)) hy⟩

/-- Weight separation and finite scalar action on the quotient identify the
original invariant subspace by a formula containing only the ambient operator. -/
theorem scalarPowerCore_eq_of_invariant
    (F : Module.End K V) (a : K) (S : Submodule K V) [FiniteDimensional K S]
    (hS : ∀ x ∈ S, F x ∈ S)
    (hno : ∀ n : ℕ+, ∀ x ∈ S, (F ^ (n : ℕ)) x = a ^ (n : ℕ) • x → x = 0)
    (hquot : ∃ n : ℕ+, ∀ x : V, (F ^ (n : ℕ)) x - a ^ (n : ℕ) • x ∈ S) :
    scalarPowerCore F a = S := by
  obtain ⟨n, hn⟩ := hquot
  apply le_antisymm
  · exact (iInf_le (fun m : ℕ+ => LinearMap.range (scalarPowerDifference F a m)) n).trans
      (by rintro x ⟨y, rfl⟩; exact hn y)
  · apply le_iInf
    intro m
    exact le_range_scalarPowerDifference_of_no_eigenvectors F a S hS m (hno m)

/-- Intertwining the original operators intertwines all their scalar-power differences. -/
theorem intertwine_scalarPowerDifference
    (F : Module.End K V) (F' : Module.End K W) (e : V ≃ₗ[K] W)
    (he : ∀ x, e (F x) = F' (e x)) (a : K) (n : ℕ+) (x : V) :
    e (scalarPowerDifference F a n x) = scalarPowerDifference F' a n (e x) := by
  have hp : ∀ m : ℕ, ∀ y : V, e ((F ^ m) y) = (F' ^ m) (e y) := by
    intro m
    induction m with
    | zero => intro y; rfl
    | succ m ih =>
      intro y
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, he, ih]
  change e ((F ^ (n : ℕ)) x - a ^ (n : ℕ) • x) =
    (F' ^ (n : ℕ)) (e x) - a ^ (n : ℕ) • e x
  rw [map_sub, map_smul, hp]

/-- Membership in each scalar-power image is intrinsic under an intertwining equivalence. -/
theorem mem_range_scalarPowerDifference_iff
    (F : Module.End K V) (F' : Module.End K W) (e : V ≃ₗ[K] W)
    (he : ∀ x, e (F x) = F' (e x)) (a : K) (n : ℕ+) (x : V) :
    e x ∈ LinearMap.range (scalarPowerDifference F' a n) ↔
      x ∈ LinearMap.range (scalarPowerDifference F a n) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, e.injective ?_⟩
    rw [intertwine_scalarPowerDifference F F' e he, e.apply_symm_apply]
    exact hy
  · rintro ⟨y, rfl⟩
    exact ⟨e y, (intertwine_scalarPowerDifference F F' e he a n y).symm⟩

/-- The entire intrinsic subspace is preserved by the original linear equivalence. -/
theorem scalarPowerCore_map_eq
    (F : Module.End K V) (F' : Module.End K W) (e : V ≃ₗ[K] W)
    (he : ∀ x, e (F x) = F' (e x)) (a : K) :
    (scalarPowerCore F a).map e.toLinearMap = scalarPowerCore F' a := by
  have hmem (x : V) : e x ∈ scalarPowerCore F' a ↔ x ∈ scalarPowerCore F a := by
    simp only [scalarPowerCore, Submodule.mem_iInf]
    exact forall_congr' fun n => mem_range_scalarPowerDifference_iff F F' e he a n x
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mpr hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (hmem (e.symm y)).mp
    rwa [e.apply_symm_apply]

end LinearMap
