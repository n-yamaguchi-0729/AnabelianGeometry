/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Places.Evaluation.HasValueIffMemEqOrOrdSubPos
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation

/-! # Literal residue values along an unchanged normalized-order comparison

The coefficient embedding and field map are explicit. Exact orders transfer
values to the extended constant field, and rationality then identifies the
actual evalAt values, including the zero convention at a pole.
-/
noncomputable section

namespace AlgebraicCurve.Place

variable {k E F F' : Type*} [Field k] [Field E] [Field F] [Field F']
variable [Algebra k E] [Algebra k F] [Algebra E F']

/-- Exact normalized orders and the given constant embedding transfer actual
finite residue values. No rationality is assumed on the extended place. -/
theorem hasValue_of_orderCompatible
    (φ : F →+* F')
    (hcoeff : ∀ a : k, φ (algebraMap k F a) = algebraMap E F' (algebraMap k E a))
    (V : Place k F) (W : Place E F')
    (hord : ∀ z, W.ord (φ z) = V.ord z)
    (f : F) (hf : f ≠ 0) (a : k) (hvalue : V.HasValue f a) :
    W.HasValue (φ f) (algebraMap k E a) := by
  rw [hasValue_iff_mem_and_eq_or_ord_sub_pos] at hvalue ⊢
  refine ⟨(W.mem_iff_ord_nonneg ((map_ne_zero φ).mpr hf)).mpr ?_, ?_⟩
  · rw [hord]
    exact (V.mem_iff_ord_nonneg hf).mp hvalue.1
  · rcases hvalue.2 with h | h
    · left
      rw [h, hcoeff]
    · right
      have hsub : φ f - algebraMap E F' (algebraMap k E a) =
          φ (f - algebraMap k F a) := by rw [map_sub, hcoeff]
      rw [hsub, hord]
      exact h

/-- The original value extends by the original constant-field embedding;
there is no newly selected residue value, even at a pole. -/
theorem evalAt_eq_of_orderCompatible
    (φ : F →+* F')
    (hcoeff : ∀ a : k, φ (algebraMap k F a) = algebraMap E F' (algebraMap k E a))
    (V : Place k F) (W : Place E F') (hV : V.IsRational) (hW : W.IsRational)
    (hord : ∀ z, W.ord (φ z) = V.ord z)
    (f : F) (hf : f ≠ 0) : W.evalAt (φ f) = algebraMap k E (V.evalAt f) := by
  classical
  have hmem : φ f ∈ W.toValuationSubring ↔ f ∈ V.toValuationSubring := by
    rw [W.mem_iff_ord_nonneg ((map_ne_zero φ).mpr hf), V.mem_iff_ord_nonneg hf, hord]
  by_cases h : f ∈ V.toValuationSubring
  · have hWmem := hmem.mpr h
    have hval : V.HasValue f (V.evalAt f) := ⟨h, (V.algebraMap_evalAt hV h).symm⟩
    have hWval : W.HasValue (φ f) (W.evalAt (φ f)) :=
      ⟨hWmem, (W.algebraMap_evalAt hW hWmem).symm⟩
    exact hWval.unique (hasValue_of_orderCompatible φ hcoeff V W hord f hf _ hval)
  · have h' : φ f ∉ W.toValuationSubring := fun hm => h (hmem.mp hm)
    simp only [evalAt, dite_eq_right h, dite_eq_right h', map_zero]

end AlgebraicCurve.Place
