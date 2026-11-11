/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Traces on finite families of vector spaces

The trace of an operator on a finite product is the sum of its diagonal
blocks. For an operator carrying one component to another, only fixed
components contribute. The components may have different dimensions; no
choice of bases or equivariant trivializations is an input.
-/

@[expose] public section

noncomputable section

universe u v w v'

namespace EtaleCohomology

section Diagonal

variable {K : Type u} [Semiring K] {ι : Type w} [DecidableEq ι]
  (V : ι → Type v) [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]

/-- The diagonal block of an operator carrying coordinate `σ i` to coordinate `i`.
The family structures are shared by projection, inclusion, and composition. -/
def finiteFamilyDiagonal (σ : ι → ι) (a : ∀ i, V (σ i) →ₗ[K] V i) (i : ι) :
    Module.End K (V i) :=
  (a i).comp ((LinearMap.proj (σ i)).comp (LinearMap.single K V i))

/-- A coordinate which is not fixed has zero diagonal block. -/
theorem finiteFamilyDiagonal_eq_zero (σ : ι → ι)
    (a : ∀ i, V (σ i) →ₗ[K] V i) (i : ι) (hi : σ i ≠ i) :
    finiteFamilyDiagonal V σ a i = 0 := by
  unfold finiteFamilyDiagonal
  rw [LinearMap.proj_comp_single_ne K V (σ i) i hi]
  exact LinearMap.comp_zero (a i)

end Diagonal

variable {K : Type u} [Field K] {ι : Type w} [Fintype ι] [DecidableEq ι]
  (V : ι → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  [∀ i, FiniteDimensional K (V i)]

/-- Trace on a finite family is the sum of the traces of its actual diagonal
blocks, without a choice of bases. -/
theorem trace_finiteFamily (f : (∀ i, V i) →ₗ[K] (∀ i, V i)) :
    LinearMap.trace K (∀ i, V i) f =
      ∑ i, LinearMap.trace K (V i)
        ((LinearMap.proj i).comp (f.comp (LinearMap.single K V i))) := by
  have hid : (∑ i, (LinearMap.single K V i).comp (LinearMap.proj i)) =
      LinearMap.id := by
    apply LinearMap.ext
    intro x
    simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.single_apply, LinearMap.id_apply] using LinearMap.sum_single_apply V x
  calc
    LinearMap.trace K (∀ i, V i) f =
        LinearMap.trace K (∀ i, V i)
          ((∑ i, (LinearMap.single K V i).comp (LinearMap.proj i)).comp f) := by
      rw [hid, LinearMap.id_comp]
    _ = ∑ i, LinearMap.trace K (∀ i, V i)
        (((LinearMap.single K V i).comp (LinearMap.proj i)).comp f) := by
      have hs : ((∑ i, (LinearMap.single K V i).comp (LinearMap.proj i)).comp f) =
          ∑ i, (((LinearMap.single K V i).comp (LinearMap.proj i)).comp f) := by
        apply LinearMap.ext
        intro x
        simp only [LinearMap.comp_apply, LinearMap.sum_apply]
      rw [hs, map_sum]
    _ = ∑ i, LinearMap.trace K (V i)
        ((LinearMap.proj i).comp (f.comp (LinearMap.single K V i))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [LinearMap.comp_assoc, LinearMap.trace_comp_comm', LinearMap.comp_assoc]

/-- An operator between components has trace supported on the fixed
components of its index map. The displayed diagonal block includes the
canonical transport when the source and target indices agree. -/
theorem trace_finiteFamily_eq_sum_fixed (σ : ι → ι)
    (a : ∀ i, V (σ i) →ₗ[K] V i) :
    LinearMap.trace K (∀ i, V i)
        (LinearMap.pi (fun i => (a i).comp (LinearMap.proj (σ i)))) =
      ∑ i ∈ Finset.univ.filter (fun i => σ i = i),
        LinearMap.trace K (V i)
          ((a i).comp ((LinearMap.proj (σ i)).comp (LinearMap.single K V i))) := by
  rw [trace_finiteFamily, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [← LinearMap.comp_assoc, LinearMap.proj_pi, LinearMap.comp_assoc]
  by_cases hi : σ i = i
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi, LinearMap.proj_comp_single_ne K V (σ i) i hi,
      LinearMap.comp_zero, map_zero]

omit [Fintype ι] in
/-- Conjugating an operator to its actual finite-family action expresses its
trace as the finite sum of the diagonal blocks at the fixed indices. -/
theorem trace_finiteFamily_conj_eq_finsum_fixed
    [Finite ι] {W : Type v'} [AddCommGroup W] [Module K W]
    (E : W ≃ₗ[K] (∀ i, V i)) (T : W →ₗ[K] W)
    (σ : ι → ι) (a : ∀ i, V (σ i) →ₗ[K] V i)
    (hconj : E.conj T =
      LinearMap.pi (fun i => (a i).comp (LinearMap.proj (σ i)))) :
    LinearMap.trace K W T =
      ∑ᶠ z : {i : ι // σ i = i},
        LinearMap.trace K (V z.val)
          ((a z.val).comp
            ((LinearMap.proj (σ z.val)).comp (LinearMap.single K V z.val))) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let d : ι → K := fun i =>
    LinearMap.trace K (V i)
      ((a i).comp ((LinearMap.proj (σ i)).comp (LinearMap.single K V i)))
  calc
    LinearMap.trace K W T =
        LinearMap.trace K (∀ i, V i) (E.conj T) :=
      (LinearMap.trace_conj' T E).symm
    _ = LinearMap.trace K (∀ i, V i)
        (LinearMap.pi (fun i => (a i).comp (LinearMap.proj (σ i)))) :=
      congrArg (LinearMap.trace K (∀ i, V i)) hconj
    _ = ∑ i ∈ Finset.univ.filter (fun i => σ i = i), d i :=
      trace_finiteFamily_eq_sum_fixed V σ a
    _ = ∑ z : {i : ι // σ i = i}, d z.val :=
      Finset.sum_subtype _ (fun z => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]) d
    _ = ∑ᶠ z : {i : ι // σ i = i}, d z.val :=
      (finsum_eq_sum_of_fintype _).symm

omit [Fintype ι] in
/-- The fixed-component trace formula expressed through the abstract diagonal
operation, so specialization preserves the shared family structures. -/
theorem trace_finiteFamily_conj_eq_finsum_diagonal
    [Finite ι] {W : Type v'} [AddCommGroup W] [Module K W]
    (E : W ≃ₗ[K] (∀ i, V i)) (T : W →ₗ[K] W)
    (σ : ι → ι) (a : ∀ i, V (σ i) →ₗ[K] V i)
    (hconj : E.conj T =
      LinearMap.pi (fun i => (a i).comp (LinearMap.proj (σ i)))) :
    LinearMap.trace K W T =
      ∑ᶠ z : {i : ι // σ i = i},
        LinearMap.trace K (V z.val) (finiteFamilyDiagonal V σ a z.val) :=
  trace_finiteFamily_conj_eq_finsum_fixed V E T σ a hconj

end EtaleCohomology
