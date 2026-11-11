/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Tactic.Choose

/-!
# Finitely supported coboundaries of a cyclic permutation

If the fibers of a surjection are the orbits of a permutation, a finitely
supported integer function whose sum on each fiber is zero is a difference
under that permutation. The primitive is a finite sum of orbit segments.
Its support stays over the image of the original support.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace CyclicAction

variable {S T : Type*}

private def permutationOrbitSegment (σ : Equiv.Perm S) (x : S) (n : ℕ) (m : ℤ) :
    S →₀ ℤ :=
  ∑ i ∈ Finset.range n, Finsupp.single ((σ ^ i) x) m

private theorem permutationOrbitSegment_coboundary
    (σ : Equiv.Perm S) (x : S) (n : ℕ) (m : ℤ) :
    Finsupp.mapDomain σ (permutationOrbitSegment σ x n m) -
        permutationOrbitSegment σ x n m =
      Finsupp.single ((σ ^ n) x) m - Finsupp.single x m := by
  classical
  unfold permutationOrbitSegment
  rw [Finsupp.mapDomain_finsetSum, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ i ∈ Finset.range n,
        (Finsupp.single ((σ ^ (i + 1)) x) m - Finsupp.single ((σ ^ i) x) m) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finsupp.mapDomain_single, pow_succ', Equiv.Perm.mul_apply]
    _ = _ := by
      simpa only [pow_zero, Equiv.Perm.one_apply] using
        Finset.sum_range_sub (fun i => Finsupp.single ((σ ^ i) x) m) n

/-- A finitely supported integer function of fiber sum zero is an actual
permutation coboundary. Its primitive uses only fibers meeting the original
support; no finiteness of the ambient set or of its orbit space is required. -/
theorem exists_permutation_coboundary_of_mapDomain_eq_zero
    (σ : Equiv.Perm S) (r : S → T) (hr : Function.Surjective r)
    (hrσ : ∀ x, r (σ x) = r x)
    (hOrbit : ∀ x y, r x = r y → ∃ n : ℕ, (σ ^ n) x = y)
    (D : S →₀ ℤ) (hD : Finsupp.mapDomain r D = 0) :
    ∃ C : S →₀ ℤ, Finsupp.mapDomain σ C - C = D ∧
      (C.support : Set S) ⊆ r ⁻¹' (r '' (D.support : Set S)) := by
  classical
  choose s hs using hr
  have hreach (x : S) : ∃ n : ℕ, (σ ^ n) (s (r x)) = x :=
    hOrbit (s (r x)) x (hs (r x))
  choose n hn using hreach
  let C : S →₀ ℤ := D.sum fun x m => permutationOrbitSegment σ (s (r x)) (n x) m
  refine ⟨C, ?_, ?_⟩
  · change Finsupp.mapDomain σ (D.sum _) - D.sum _ = D
    rw [Finsupp.mapDomain_sum, ← Finsupp.sum_sub]
    calc
      _ = D.sum (fun x m => Finsupp.single x m - Finsupp.single (s (r x)) m) := by
        apply Finsupp.sum_congr
        intro x _
        rw [permutationOrbitSegment_coboundary, hn]
      _ = D - Finsupp.mapDomain s (Finsupp.mapDomain r D) := by
        rw [Finsupp.sum_sub, Finsupp.sum_single, ← Finsupp.mapDomain_fun_comp,
          Finsupp.mapDomain]
      _ = D := by rw [hD, Finsupp.mapDomain_zero, sub_zero]
  · have hpow (i : ℕ) (x : S) : r ((σ ^ i) x) = r x := by
      induction i with
      | zero => simp only [pow_zero, Equiv.Perm.one_apply]
      | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, hrσ, ih]
    intro y hy
    change y ∈ (∑ x ∈ D.support,
      permutationOrbitSegment σ (s (r x)) (n x) (D x)).support at hy
    obtain ⟨x, hx, hy⟩ := Finsupp.mem_support_finsetSum y hy
    change y ∈ (∑ i ∈ Finset.range (n x),
      Finsupp.single ((σ ^ i) (s (r x))) (D x)).support at hy
    obtain ⟨i, _, hy⟩ := Finsupp.mem_support_finsetSum y hy
    have hpoint : y = (σ ^ i) (s (r x)) :=
      Finset.mem_singleton.mp (Finsupp.support_single_subset hy)
    refine ⟨x, hx, ?_⟩
    rw [hpoint, hpow, hs]

end CyclicAction
