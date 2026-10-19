/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineStandardPlace
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # Rational places in the fibers of the square coordinate

Every place above a selected value of X squared is the standard place of a
selected square root or its negative. The pole fiber is the infinite place.
These results classify places and prove their rationality from the given roots.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open AlgebraicCurve AlgebraicGeometry.ProjSpace
open scoped RatFunc

namespace AnabelianGeometry.KummerTheory

variable {k : Type} [Field k]

/-- Every place where X squared has the selected finite value is one of the
two literal standard places at the selected root and its negative. -/
theorem ratFunc_eq_standardPlace_of_hasValue_square
    (V : Place k (RatFunc k)) (a r : k) (hr : r ^ 2 = a)
    (hV : V.HasValue ((RatFunc.X : RatFunc k) ^ 2) a) :
    V = RationalFunctionField.placeOfPoint k r ∨
      V = RationalFunctionField.placeOfPoint k (-r) := by
  classical
  have hlin (c : k) :
      algebraMap (Polynomial k) (RatFunc k) (Polynomial.X - Polynomial.C c) =
        RatFunc.X - algebraMap k (RatFunc k) c := by
    rw [map_sub, RatFunc.algebraMap_X, ← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k)]
  have hne (c : k) :
      algebraMap (Polynomial k) (RatFunc k) (Polynomial.X - Polynomial.C c) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero c)
  have hfactor :
      (RatFunc.X : RatFunc k) ^ 2 - algebraMap k (RatFunc k) a =
        algebraMap (Polynomial k) (RatFunc k) (Polynomial.X - Polynomial.C r) *
        algebraMap (Polynomial k) (RatFunc k) (Polynomial.X - Polynomial.C (-r)) := by
    rw [hlin r, hlin (-r), map_neg, ← hr, map_pow]
    ring
  have hnonzero : (RatFunc.X : RatFunc k) ^ 2 - algebraMap k (RatFunc k) a ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero (hne r) (hne (-r))
  have hpos : 0 < V.ord ((RatFunc.X : RatFunc k) ^ 2 -
      algebraMap k (RatFunc k) a) := by
    rcases ((V.hasValue_iff_mem_and_eq_or_ord_sub_pos _ a).mp hV).2 with he | he
    · exact (hnonzero (sub_eq_zero.mpr he)).elim
    · exact he
  by_cases hp : V = RationalFunctionField.placeOfPoint k r
  · exact Or.inl hp
  by_cases hm : V = RationalFunctionField.placeOfPoint k (-r)
  · exact Or.inr hm
  rw [hfactor, V.ord_mul (hne r) (hne (-r)),
    RationalFunctionField.ord_X_sub_C, RationalFunctionField.ord_X_sub_C,
    Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.single_eq_of_ne hp, Finsupp.single_eq_of_ne hm] at hpos
  by_cases hI : V = RationalFunctionField.placeInfty k
  · rw [hI, Finsupp.single_eq_same] at hpos
    norm_num at hpos
  · rw [Finsupp.single_eq_of_ne hI] at hpos
    norm_num at hpos

/-- The finite-fibre rationality conclusion is proved, not assumed. -/
theorem ratFunc_isRational_of_hasValue_square
    (V : Place k (RatFunc k)) (a r : k) (hr : r ^ 2 = a)
    (hV : V.HasValue ((RatFunc.X : RatFunc k) ^ 2) a) : V.IsRational := by
  have hrat (c : k) : (RationalFunctionField.placeOfPoint k c).IsRational := by
    have hv : (c, (1 : k)) ≠ 0 := fun h => one_ne_zero (congrArg Prod.snd h)
    have he := literalRationalPuncturePlace_eq_placeOfPoint k (c, 1) hv one_ne_zero
    simp only [div_one] at he
    rw [← he]
    exact literalRationalPuncturePlace_isRational k (c, 1) hv
  rcases ratFunc_eq_standardPlace_of_hasValue_square V a r hr hV with h | h
  · rw [h]
    exact hrat r
  · rw [h]
    exact hrat (-r)

/-- The pole fibre of the same square coordinate is the original infinite
standard place. -/
theorem ratFunc_eq_placeInfty_of_square_ord_neg
    (V : Place k (RatFunc k))
    (hneg : V.ord ((RatFunc.X : RatFunc k) ^ 2) < 0) :
    V = RationalFunctionField.placeInfty k := by
  classical
  by_contra hI
  have hX0 :
      algebraMap (Polynomial k) (RatFunc k) (Polynomial.X - Polynomial.C 0) =
        RatFunc.X := by rw [Polynomial.C_0, sub_zero, RatFunc.algebraMap_X]
  have hxnonneg : 0 ≤ V.ord (RatFunc.X : RatFunc k) := by
    rw [← hX0, RationalFunctionField.ord_X_sub_C, Finsupp.add_apply,
      Finsupp.single_eq_of_ne hI, add_zero]
    by_cases h0 : V = RationalFunctionField.placeOfPoint k 0
    · rw [h0, Finsupp.single_eq_same]
      norm_num
    · rw [Finsupp.single_eq_of_ne h0]
  have hxne : (RatFunc.X : RatFunc k) ≠ 0 := by
    rw [← RatFunc.algebraMap_X]
    exact RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  rw [pow_two, V.ord_mul hxne hxne] at hneg
  omega

/-- Exhaustion of an arbitrary finite family of square fibres, including
the pole fibre. The finite values and chosen roots are unchanged. -/
theorem ratFunc_eq_standardPlace_of_square_boundary
    {ι : Type} (v r : ι → k) (hr : ∀ i, r i ^ 2 = v i)
    (V : Place k (RatFunc k))
    (hV : V.ord ((RatFunc.X : RatFunc k) ^ 2) < 0 ∨
      ∃ i, V.HasValue ((RatFunc.X : RatFunc k) ^ 2) (v i)) :
    V = RationalFunctionField.placeInfty k ∨
      ∃ i, V = RationalFunctionField.placeOfPoint k (r i) ∨
        V = RationalFunctionField.placeOfPoint k (-(r i)) := by
  rcases hV with h | ⟨i, h⟩
  · exact Or.inl (ratFunc_eq_placeInfty_of_square_ord_neg V h)
  · exact Or.inr ⟨i, ratFunc_eq_standardPlace_of_hasValue_square V (v i) (r i) (hr i) h⟩

/-- All inverse-image boundary places satisfying the original square-coordinate
value/pole condition are rational, including every finite fibre and infinity. -/
theorem ratFunc_isRational_of_square_boundary
    {ι : Type} (v r : ι → k) (hr : ∀ i, r i ^ 2 = v i)
    (V : Place k (RatFunc k))
    (hV : V.ord ((RatFunc.X : RatFunc k) ^ 2) < 0 ∨
      ∃ i, V.HasValue ((RatFunc.X : RatFunc k) ^ 2) (v i)) : V.IsRational := by
  rcases hV with h | ⟨i, h⟩
  · rw [ratFunc_eq_placeInfty_of_square_ord_neg V h]
    have hv : ((1 : k), (0 : k)) ≠ 0 := fun he => one_ne_zero (congrArg Prod.fst he)
    rw [← literalRationalPuncturePlace_eq_placeInfty k (1, 0) hv rfl]
    exact literalRationalPuncturePlace_isRational k (1, 0) hv
  · exact ratFunc_isRational_of_hasValue_square V (v i) (r i) (hr i) h

end AnabelianGeometry.KummerTheory
