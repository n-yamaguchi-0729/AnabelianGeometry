/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Divisors.Correspondences.Correspondences
import Nyll.AlgebraicCurves.Places.Evaluation.HasValueIffMemEqOrOrdSubPos
import Nyll.AlgebraicCurves.Places.Ramification.OneLeRamificationIndex
import Lean.Elab.Tactic.Omega

/-! # Literal values and poles under restriction along an integral field map

The actual restricted place and the actual field homomorphism are retained.
No source-place rationality, unramifiedness, or residue identification is needed.
-/
noncomputable section

namespace AlgebraicCurve.Place

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F']

/-- Values in the unchanged coefficient field are preserved and reflected by
restriction along the given integral field homomorphism. -/
theorem hasValue_restrictAlong_iff
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) (a : K) :
    (w.restrictAlong φ hφ).HasValue f a ↔ w.HasValue (φ f) a := by
  have hmem : f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔
      φ f ∈ w.toValuationSubring := Iff.rfl
  have hepos : 0 < (Place.ramificationIndexAlong φ w : ℤ) := by
    have he := Place.one_le_ramificationIndexAlong φ hφ w
    omega
  have heq : f = algebraMap K F a ↔ φ f = algebraMap K F' a := by
    constructor
    · intro h
      rw [h, φ.commutes]
    · intro h
      exact φ.injective (h.trans (φ.commutes a).symm)
  have hord :
      w.ord (φ f - algebraMap K F' a) =
        Place.ramificationIndexAlong φ w *
          (w.restrictAlong φ hφ).ord (f - algebraMap K F a) := by
    rw [← φ.commutes a, ← map_sub, Place.ord_restrictAlong φ hφ]
  rw [hasValue_iff_mem_and_eq_or_ord_sub_pos,
    hasValue_iff_mem_and_eq_or_ord_sub_pos, hmem, heq, hord,
    mul_pos_iff_of_pos_left hepos]

/-- Strictly negative orders are also preserved and reflected; the
ramification index is positive, rather than being assumed to equal one. -/
theorem ord_restrictAlong_neg_iff
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    (w.restrictAlong φ hφ).ord f < 0 ↔ w.ord (φ f) < 0 := by
  have hepos : 0 < (Place.ramificationIndexAlong φ w : ℤ) := by
    have he := Place.one_le_ramificationIndexAlong φ hφ w
    omega
  rw [Place.ord_restrictAlong φ hφ]
  constructor
  · intro h
    exact mul_neg_of_pos_of_neg hepos h
  · intro h
    by_contra hn
    have hn' : 0 ≤ (w.restrictAlong φ hφ).ord f := le_of_not_gt hn
    exact (not_lt_of_ge (mul_nonneg hepos.le hn')) h

/-- Direct finite-value input for an unchanged root-coordinate equation. -/
theorem hasValue_of_restrictAlong_eq
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (v : Place K F)
    (hw : w.restrictAlong φ hφ = v)
    (f : F) (a : K) (hf : v.HasValue f a) :
    w.HasValue (φ f) a := by
  apply (hasValue_restrictAlong_iff φ hφ w f a).mp
  rwa [hw]

/-- Direct pole input for the actual restricted place. -/
theorem ord_neg_of_restrictAlong_eq
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (v : Place K F)
    (hw : w.restrictAlong φ hφ = v)
    (f : F) (hf : v.ord f < 0) : w.ord (φ f) < 0 := by
  apply (ord_restrictAlong_neg_iff φ hφ w f).mp
  rwa [hw]

end AlgebraicCurve.Place
