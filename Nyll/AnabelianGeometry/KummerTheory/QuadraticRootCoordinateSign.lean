/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Commute

/-! # A global sign is the only ambiguity in a quadratic fibre coordinate

This compares two coordinates on the SAME fibre with the SAME square equation.
It does not compare roots chosen on different covers. Changing such a coordinate
therefore preserves every ratio normalized at a retained point of that fibre.
-/
noncomputable section

namespace AnabelianGeometry.KummerTheory

/-- Two bijective coordinates on the same quadratic root fibre differ by one
sign, independent of the point. No compatibility of arbitrary roots is assumed. -/
theorem quadraticRootCoordinates_differ_by_sign
    {F T : Type*} [Field F] {a : F}
    (e e' : T ≃ {z : F // z ^ 2 = a}) (x₀ : T) :
    (∀ x, (e' x).val = (e x).val) ∨
      ∀ x, (e' x).val = -(e x).val := by
  classical
  have hother (q : T ≃ {z : F // z ^ 2 = a}) (x : T) (hx : x ≠ x₀) :
      (q x).val = -(q x₀).val := by
    have hsq : (q x).val ^ 2 = (q x₀).val ^ 2 :=
      (q x).property.trans (q x₀).property.symm
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact (hx (q.injective (Subtype.ext h))).elim
    · exact h
  have hbase : (e' x₀).val ^ 2 = (e x₀).val ^ 2 :=
    (e' x₀).property.trans (e x₀).property.symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hbase with h | h
  · left
    intro x
    by_cases hx : x = x₀
    · subst x
      exact h
    · rw [hother e' x hx, h, hother e x hx]
  · right
    intro x
    by_cases hx : x = x₀
    · subst x
      exact h
    · rw [hother e' x hx, h, hother e x hx]

/-- Normalization at the same retained point cancels the sole sign ambiguity. -/
theorem quadraticRootCoordinates_normalized_ratio_eq
    {F T : Type*} [Field F] {a : F}
    (e e' : T ≃ {z : F // z ^ 2 = a}) (x c : T) :
    (e' x).val / (e' c).val = (e x).val / (e c).val := by
  rcases quadraticRootCoordinates_differ_by_sign e e' c with h | h
  · rw [h x, h c]
  · simp only [h x, h c, div_eq_mul_inv, inv_neg, neg_mul_neg]

end AnabelianGeometry.KummerTheory
