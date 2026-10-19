/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Mathlib.LinearAlgebra.Dimension.Finrank
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom

/-!
# OModule Presheaf Euler Char
-/

noncomputable section

universe u

namespace AlgebraicGeometry.OModulePresheaf

open CategoryTheory

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

/-- The rank of Čech cohomology in the specified degree. -/
def cechFinrank : ℕ → ℕ
  | 0 => Module.finrank R (F.H0 K)
  | i + 1 => Module.finrank R (F.HSucc K i)

theorem cechFinrank_zero : F.cechFinrank K 0 = Module.finrank R (F.H0 K) := rfl

theorem cechFinrank_succ (i : ℕ) : F.cechFinrank K (i + 1) = Module.finrank R (F.HSucc K i) := rfl

/-- The alternating sum of the ranks of Čech cohomology for the finite cover. -/
def eulerChar : ℤ :=
  ∑ i ∈ Finset.range (Fintype.card K.ι), (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ)

theorem eulerChar_def :
    F.eulerChar K = ∑ i ∈ Finset.range (Fintype.card K.ι), (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ)
      := rfl

/-- The Euler characteristic vanishes when all affine sections are subsingletons.
Proof consolidated from the Anthropic FLT-derived coefficient formula for twisted Euler
characteristics in this directory. -/
theorem eulerChar_eq_zero_of_subsingleton [Nontrivial R] [IsSeparated π]
    (hF : ∀ U : V.affineOpens, Subsingleton (F.obj U.1)) : F.eulerChar K = 0 := by
  have hco : ∀ i, Subsingleton (F.cochain K i) := fun i => by
    have : ∀ s : K.Idx i, Subsingleton (F.obj (K.inter s)) := fun s => hF (K.affineInter π s)
    infer_instance
  have hcf : ∀ i, F.cechFinrank K i = 0 := by
    intro i
    cases i with
    | zero =>
      have := hco 0
      have : Subsingleton (F.H0 K) := inferInstance
      exact Module.finrank_zero_of_subsingleton
    | succ j =>
      have := hco (j + 1)
      have : Subsingleton (F.HSucc K j) := inferInstance
      exact Module.finrank_zero_of_subsingleton
  rw [OModulePresheaf.eulerChar_def]
  exact Finset.sum_eq_zero fun i _ => by rw [hcf i, Nat.cast_zero, mul_zero]

end AlgebraicGeometry.OModulePresheaf

end
