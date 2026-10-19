/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.KummerTheory.RatFuncCoordinatePlaceUniqueness
import Nyll.SchemeTheory.ProjectiveSpace.Normalization

/-! Actual place restriction determines the square of the retained root coordinate.
Literal cross-ratio formulas identify its normalized value and complement. -/

noncomputable section
open AlgebraicCurve
open scoped RatFunc
namespace AnabelianGeometry.KummerTheory

/-- The value at the already retained upstairs place satisfies the actual
square equation. The place, coordinate value, and downstairs value are inputs;
no root is selected in this proof. -/
theorem actualSquareRootValue_sq
    {K : Type} [Field K]
    (e : RatFunc K ≃ₐ[K] RatFunc K) (f : RatFunc K)
    (hf : e RatFunc.X = f) (V W : Place K (RatFunc K))
    (hrestrict : W.restrictAlong (ratFuncPairSquareHom e)
      (ratFuncPairSquareHom_isIntegral e) = V)
    (a r : K) (hV : V.HasValue f a)
    (hW : W.HasValue (RatFunc.X : RatFunc K) r) : r ^ 2 = a := by
  have h := Place.hasValue_of_restrictAlong_eq (ratFuncPairSquareHom e)
    (ratFuncPairSquareHom_isIntegral e) W V hrestrict f a hV
  rw [ratFuncPairSquareHom_apply_pair e f hf] at h
  have hr : W.HasValue ((RatFunc.X : RatFunc K) ^ 2) (r ^ 2) := by
    simpa only [pow_two] using hW.mul hW
  exact hr.unique h

/-- Normalize at the SAME selected reference lift. This applies unchanged to
the target points obtained by the single retained puncture equivalence. -/
theorem actualSquareRootValue_ratio_sq
    {K : Type} [Field K]
    (e : RatFunc K ≃ₐ[K] RatFunc K) (f : RatFunc K)
    (hf : e RatFunc.X = f) (V₀ V W₀ W : Place K (RatFunc K))
    (hrestrict₀ : W₀.restrictAlong (ratFuncPairSquareHom e)
      (ratFuncPairSquareHom_isIntegral e) = V₀)
    (hrestrict : W.restrictAlong (ratFuncPairSquareHom e)
      (ratFuncPairSquareHom_isIntegral e) = V)
    (a₀ a r₀ r : K) (hV₀ : V₀.HasValue f a₀) (hV : V.HasValue f a)
    (hW₀ : W₀.HasValue (RatFunc.X : RatFunc K) r₀)
    (hW : W.HasValue (RatFunc.X : RatFunc K) r) :
    (r / r₀) ^ 2 = a / a₀ := by
  rw [div_pow, actualSquareRootValue_sq e f hf V W hrestrict a r hV hW,
    actualSquareRootValue_sq e f hf V₀ W₀ hrestrict₀ a₀ r₀ hV₀ hW₀]

end AnabelianGeometry.KummerTheory

namespace AnabelianGeometry.ProjectiveLine

/-- Literal standard root-coordinate cross ratio, with its retained reference
point. This requires no sign convention on either root. -/
theorem crossRatio_standard_root_coordinate
    {K : Type} [Field K] (r₀ r : K) :
    crossRatio (affinePoint (0 : K)) infinityPoint (affinePoint r₀) (affinePoint r) =
      r / r₀ := by
  simp [affinePoint, infinityPoint, crossRatio_mk, homogeneousCrossRatio, bracket]

/-- Exchanging the zero and reference labels produces the complement under
this project's actual cross-ratio convention. -/
theorem crossRatio_swap_first_third_complement
    {K : Type} [Field K] (a b c d : Projectivization K (K × K))
    (hca : c ≠ a) (hdb : d ≠ b) :
    crossRatio c b a d = 1 - crossRatio a b c d := by
  have hca' : bracket c.rep a.rep ≠ 0 :=
    fun h => hca ((bracket_rep_eq_zero_iff c a).mp h)
  have hac' : bracket a.rep c.rep ≠ 0 :=
    fun h => hca ((bracket_rep_eq_zero_iff a c).mp h).symm
  have hdb' : bracket d.rep b.rep ≠ 0 :=
    fun h => hdb ((bracket_rep_eq_zero_iff d b).mp h)
  change homogeneousCrossRatio c.rep b.rep a.rep d.rep =
    1 - homogeneousCrossRatio a.rep b.rep c.rep d.rep
  unfold homogeneousCrossRatio
  field_simp [hca', hac', hdb']
  unfold bracket
  ring

end AnabelianGeometry.ProjectiveLine
