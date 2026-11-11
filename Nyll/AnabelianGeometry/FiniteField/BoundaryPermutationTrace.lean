/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.EllAdicBoundaryFrobenius
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Trace of the actual boundary permutation

The full permutation representation has trace equal to the number of fixed
boundary places. On a nonempty boundary the sum-zero relation removes exactly
one from that trace. A projection along one coordinate proves this by cyclic
invariance of trace; the chosen coordinate need not be Frobenius-fixed.

Scalar extension then gives the trace of the exact first-Frobenius action
constructed on the original rational boundary quotient. Nonrational boundary
points are retained throughout the calculation.
-/

@[expose] public section

universe uGeom uField

noncomputable section

open AlgebraicGeometry AlgebraicCurve
open scoped BigOperators TensorProduct

namespace AnabelianGeometry.FiniteField

variable {K : Type uGeom} {F : Type uField} [Field K] [Field F] [Algebra K F]
  (M : CurveModel K F) {X : Scheme.{uGeom}} (j : X ⟶ M.C)
  [Finite (M.openBoundaryPlaces j)] (ℓ : ℕ) [Fact ℓ.Prime]

private local instance permutationBoundaryFintype : Fintype (M.openBoundaryPlaces j) :=
  Fintype.ofFinite _

private def fullBoundaryPermutation (e : Equiv.Perm (M.openBoundaryPlaces j)) :
    Module.End ℤ_[ℓ] (M.openBoundaryPlaces j → ℤ_[ℓ]) where
  toFun a v := a (e v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem trace_fullBoundaryPermutation (e : Equiv.Perm (M.openBoundaryPlaces j)) :
    LinearMap.trace ℤ_[ℓ] (M.openBoundaryPlaces j → ℤ_[ℓ])
        (fullBoundaryPermutation M j ℓ e) =
      (Nat.card {v : M.openBoundaryPlaces j // e v = v} : ℤ_[ℓ]) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℤ_[ℓ]
    (Pi.basisFun ℤ_[ℓ] (M.openBoundaryPlaces j))]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    Pi.basisFun_apply, Pi.basisFun_repr]
  change (∑ v : M.openBoundaryPlaces j,
    (Pi.single v (1 : ℤ_[ℓ]) : M.openBoundaryPlaces j → ℤ_[ℓ]) (e v)) = _
  calc
    (∑ v : M.openBoundaryPlaces j,
      (Pi.single v (1 : ℤ_[ℓ]) : M.openBoundaryPlaces j → ℤ_[ℓ]) (e v)) =
        ∑ v : M.openBoundaryPlaces j, if e v = v then (1 : ℤ_[ℓ]) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : e v = v
      · rw [hv, Pi.single_eq_same]
        exact (ite_eq_left rfl).symm
      · rw [Pi.single_eq_of_ne hv, ite_eq_right hv]
    _ = ∑ v ∈ Finset.univ.filter (fun v : M.openBoundaryPlaces j => e v = v),
        (1 : ℤ_[ℓ]) := (Finset.sum_filter _ _).symm
    _ = ((Finset.univ.filter (fun v : M.openBoundaryPlaces j => e v = v)).card : ℤ_[ℓ]) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (Nat.card {v : M.openBoundaryPlaces j // e v = v} : ℤ_[ℓ]) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- For a nonempty boundary, the original sum-zero permutation
representation has trace equal to its number of fixed places minus one. -/
theorem trace_ellAdicBoundaryPermutation
    [Nonempty (M.openBoundaryPlaces j)] (e : Equiv.Perm (M.openBoundaryPlaces j)) :
    LinearMap.trace ℤ_[ℓ] (ellAdicBoundarySpace M j ℓ)
        (ellAdicBoundaryPermutation M j ℓ e).toLinearMap =
      (Nat.card {v : M.openBoundaryPlaces j // e v = v} : ℤ_[ℓ]) - 1 := by
  classical
  let S := M.openBoundaryPlaces j
  let V := S → ℤ_[ℓ]
  let B := ellAdicBoundarySpace M j ℓ
  let v₀ : S := Classical.choice inferInstance
  let δ : V := Pi.single v₀ 1
  let total : V →ₗ[ℤ_[ℓ]] ℤ_[ℓ] :=
    { toFun := fun a => ∑ v, a v
      map_add' := fun _ _ => Finset.sum_add_distrib
      map_smul' := fun c a => by
        change (∑ v : S, c • a v) = c • ∑ v : S, a v
        rw [Finset.smul_sum] }
  have hδ : total δ = 1 := by
    change (∑ v : S, (Pi.single v₀ (1 : ℤ_[ℓ])) v) = 1
    rw [Finset.sum_eq_single v₀]
    · exact Pi.single_eq_same _ _
    · intro v _ hv
      exact Pi.single_eq_of_ne hv _
    · intro h
      exact (h (Finset.mem_univ v₀)).elim
  let d : V →ₗ[ℤ_[ℓ]] V := LinearMap.id - total.smulRight δ
  have hd (a : V) : d a ∈ B := by
    change total (a - total a • δ) = 0
    rw [map_sub, map_smul, hδ, smul_eq_mul, mul_one, sub_self]
  let proj : V →ₗ[ℤ_[ℓ]] B := d.codRestrict B hd
  let T := (ellAdicBoundaryPermutation M j ℓ e).toLinearMap
  let U := fullBoundaryPermutation M j ℓ e
  have hproj : proj.comp B.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change a.val - total a.val • δ = a.val
    have ha : total a.val = 0 := a.property
    rw [ha, zero_smul, sub_zero]
  have hdecomp : U = (B.subtype.comp T).comp proj + total.smulRight (U δ) := by
    apply LinearMap.ext
    intro a
    funext v
    change a (e v) = (a (e v) - total a * δ (e v)) + total a * δ (e v)
    exact (sub_add_cancel _ _).symm
  have htrace := congrArg (LinearMap.trace ℤ_[ℓ] V) hdecomp
  rw [map_add, LinearMap.trace_smulRight] at htrace
  have hcyclic :
      LinearMap.trace ℤ_[ℓ] V ((B.subtype.comp T).comp proj) =
        LinearMap.trace ℤ_[ℓ] B T := by
    rw [LinearMap.trace_comp_cycle' T B.subtype proj, hproj, LinearMap.id_comp]
  have htotal : total (U δ) = 1 := (Equiv.sum_comp e δ).trans hδ
  rw [hcyclic, htotal] at htrace
  have hfull : LinearMap.trace ℤ_[ℓ] V U =
      (Nat.card {v : S // e v = v} : ℤ_[ℓ]) := trace_fullBoundaryPermutation M j ℓ e
  rw [hfull] at htrace
  exact eq_sub_iff_add_eq.mpr htrace.symm

/-- The actual rational boundary operator has cardinality times the fixed-place
trace. This is the first-Frobenius operator, including its nontrivial permutation. -/
theorem trace_rationalBoundaryFrobenius
    [Nonempty (M.openBoundaryPlaces j)] (q : ℕ)
    (e : Equiv.Perm (M.openBoundaryPlaces j)) :
    LinearMap.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] ellAdicBoundarySpace M j ℓ)
        ((q • (ellAdicBoundaryPermutation M j ℓ e).toLinearMap).baseChange ℚ_[ℓ]) =
      (q : ℚ_[ℓ]) * ((Nat.card {v : M.openBoundaryPlaces j // e v = v} : ℚ_[ℓ]) - 1) := by
  rw [LinearMap.trace_baseChange, map_nsmul,
    trace_ellAdicBoundaryPermutation M j ℓ e, map_nsmul,
    map_sub, map_natCast, map_one, nsmul_eq_mul]

end AnabelianGeometry.FiniteField
