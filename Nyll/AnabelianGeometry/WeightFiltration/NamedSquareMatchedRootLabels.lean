/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareBoundaryProjection
import Nyll.AnabelianGeometry.ProjectiveLine.ActualSquareRootValueRatio

/-! Actual named square-boundary projection identifies the ramification labels
and the deterministic root coordinates of the same matched punctures. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace AnabelianGeometry.ProjectiveLine
open AnabelianGeometry.KummerTheory
attribute [local instance] Classical.propDecidable
  MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AnabelianGeometry.WeightFiltration

private theorem actualLabel_eq_affine_of_finite
    {E : Type} [Field E] (z : Projectivization E (E × E)) (hz : z.rep.2 ≠ 0) :
    z = affinePoint (z.rep.1 / z.rep.2) := by
  calc
    z = Projectivization.mk E z.rep z.rep_nonzero := z.mk_rep.symm
    _ = affinePoint (z.rep.1 / z.rep.2) := by
      apply (Projectivization.mk_eq_mk_iff' E _ _ _ _).mpr
      refine ⟨z.rep.2, ?_⟩
      apply Prod.ext
      · change z.rep.2 * (z.rep.1 / z.rep.2) = z.rep.1
        exact mul_div_cancel₀ _ hz
      · exact mul_one _

section Named
variable (k E : Type) [Field k] [Field E] [Algebra k E]
variable (s : Finset (Projectivization k (k × k)))
variable (p : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
variable (eF : RatFunc E ≃ₐ[E] RatFunc E)
variable (hplaces : ∀ y : closedPoints (projectiveLineRatFuncModel E).C,
  ∃ hy : p.base y.val ∈ closedPoints (projectiveLineRatFuncModel E).C,
    (projectiveLineRatFuncModel E).placeOfPoint ⟨p.base y.val, hy⟩ =
      ((projectiveLineRatFuncModel E).placeOfPoint y).restrictAlong
        (ratFuncPairSquareHom eF) (ratFuncPairSquareHom_isIntegral eF))
variable (t : Finset (Projectivization E (E × E)))
variable (ht : ∀ z, z ∈ t ↔ projectiveRationalPoint z ∉ Set.range
  (pullback.fst p (rationalConfigurationBaseChangeChart k E s)))
variable {ι : Type} (τ : ι → t) (L : ι → s)
variable (hcomm : ∀ z, namedSquareOriginalLabelProjection k E s p eF hplaces t ht (τ z) = L z)

include hcomm

/-- The fixed τ-image has the actual restricted place of the prescribed
original label. Here L is σ ∘ pS in the two-cover application. -/
theorem namedSquare_matchedLabel_restrict (z : ι) :
    (projectiveRatFuncPlace (τ z).val).restrictAlong
      (ratFuncPairSquareHom eF) (ratFuncPairSquareHom_isIntegral eF) =
        (rationalConfigurationBoundaryPlace k E s (L z)).val := by
  have h := namedSquareOriginalLabelProjection_place k E s p eF hplaces t ht (τ z)
  rw [hcomm z] at h
  exact h.symm

/-- The selected root r is used solely to exhaust the finite fibre.
The coordinate returned is the deterministic coordinate of τ z itself,
not r or a freshly selected sign. -/
theorem namedSquare_matchedLabel_actual_root_coordinate
    (z : ι) (f : RatFunc E) (hf : eF RatFunc.X = f)
    (a r : E) (hr : r ^ 2 = a)
    (hvalue : (rationalConfigurationBoundaryPlace k E s (L z)).val.HasValue f a) :
    (τ z).val.rep.2 ≠ 0 ∧
    (τ z).val = affinePoint ((τ z).val.rep.1 / (τ z).val.rep.2) ∧
    ((τ z).val.rep.1 / (τ z).val.rep.2) ^ 2 = a := by
  have hrestrict := namedSquare_matchedLabel_restrict k E s p eF hplaces t ht τ L hcomm z
  have hfinite := (ratFuncPairSquare_fiber_iff_root_or_neg eF f hf
    (rationalConfigurationBoundaryPlace k E s (L z)).val
    (projectiveRatFuncPlace (τ z).val) a r hr hvalue).mp hrestrict
  have hfin : (τ z).val.rep.2 ≠ 0 := by
    intro hz
    have hi : projectiveRatFuncPlace (τ z).val = RationalFunctionField.placeInfty E := by
      simp only [projectiveRatFuncPlace, hz, ite_true]
    rcases hfinite with h | h
    · exact (RationalFunctionField.placeOfPoint_ne_placeInfty E r) (h.symm.trans hi)
    · exact (RationalFunctionField.placeOfPoint_ne_placeInfty E (-r)) (h.symm.trans hi)
  have hX : (projectiveRatFuncPlace (τ z).val).HasValue (RatFunc.X : RatFunc E)
      ((τ z).val.rep.1 / (τ z).val.rep.2) := by
    simpa only [projectiveRatFuncPlace, ite_eq_right hfin] using
      ratFunc_placeOfPoint_hasValue_X ((τ z).val.rep.1 / (τ z).val.rep.2)
  exact ⟨hfin, actualLabel_eq_affine_of_finite (τ z).val hfin,
    actualSquareRootValue_sq eF f hf _ _ hrestrict a _ hvalue hX⟩

/-- Zero has only one actual ramification place, so the same τ sends a label
above the matched zero cusp to the literal zero place. -/
theorem namedSquare_matchedLabel_zero_place
    (z : ι) (f : RatFunc E) (hf : eF RatFunc.X = f)
    (hvalue : (rationalConfigurationBoundaryPlace k E s (L z)).val.HasValue f 0) :
    projectiveRatFuncPlace (τ z).val = RationalFunctionField.placeOfPoint E 0 := by
  have hrestrict := namedSquare_matchedLabel_restrict k E s p eF hplaces t ht τ L hcomm z
  have h := (ratFuncPairSquare_fiber_iff_root_or_neg eF f hf
    (rationalConfigurationBoundaryPlace k E s (L z)).val
    (projectiveRatFuncPlace (τ z).val) 0 0 (by ring) hvalue).mp hrestrict
  simpa only [neg_zero, or_self] using h

/-- The same actual restriction identifies the unique pole ramification place. -/
theorem namedSquare_matchedLabel_infty_place
    (z : ι) (f : RatFunc E) (hf : eF RatFunc.X = f)
    (hvalue : (rationalConfigurationBoundaryPlace k E s (L z)).val.ord f < 0) :
    projectiveRatFuncPlace (τ z).val = RationalFunctionField.placeInfty E := by
  have hrestrict := namedSquare_matchedLabel_restrict k E s p eF hplaces t ht τ L hcomm z
  have h := Place.ord_neg_of_restrictAlong_eq (ratFuncPairSquareHom eF)
    (ratFuncPairSquareHom_isIntegral eF) _ _ hrestrict f hvalue
  rw [ratFuncPairSquareHom_apply_pair eF f hf] at h
  exact ratFunc_eq_placeInfty_of_square_ord_neg _ h


/-- Both values are extracted from the same τ, with the same retained
reference lift z₀. No independent sign decisions enter their ratio. -/
theorem namedSquare_matchedLabel_actual_root_ratio
    (z₀ z : ι) (f : RatFunc E) (hf : eF RatFunc.X = f)
    (a₀ a r₀ r : E) (hr₀ : r₀ ^ 2 = a₀) (hr : r ^ 2 = a)
    (hvalue₀ : (rationalConfigurationBoundaryPlace k E s (L z₀)).val.HasValue f a₀)
    (hvalue : (rationalConfigurationBoundaryPlace k E s (L z)).val.HasValue f a) :
    (((τ z).val.rep.1 / (τ z).val.rep.2) /
      ((τ z₀).val.rep.1 / (τ z₀).val.rep.2)) ^ 2 = a / a₀ := by
  have h₀ := namedSquare_matchedLabel_actual_root_coordinate
    k E s p eF hplaces t ht τ L hcomm z₀ f hf a₀ r₀ hr₀ hvalue₀
  have h := namedSquare_matchedLabel_actual_root_coordinate
    k E s p eF hplaces t ht τ L hcomm z f hf a r hr hvalue
  rw [div_pow, h.2.2, h₀.2.2]


/-- The actual zero ramification place is the literal zero projective label. -/
theorem namedSquare_matchedLabel_zero
    (z : ι) (f : RatFunc E) (hf : eF RatFunc.X = f)
    (hvalue : (rationalConfigurationBoundaryPlace k E s (L z)).val.HasValue f 0) :
    (τ z).val = affinePoint (0 : E) := by
  have h := namedSquare_matchedLabel_actual_root_coordinate
    k E s p eF hplaces t ht τ L hcomm z f hf 0 0 (by ring) hvalue
  have hr : (τ z).val.rep.1 / (τ z).val.rep.2 = 0 := by
    have hh : ((τ z).val.rep.1 / (τ z).val.rep.2) *
        ((τ z).val.rep.1 / (τ z).val.rep.2) = 0 := by
      simpa only [pow_two] using h.2.2
    rcases mul_eq_zero.mp hh with hh | hh <;> exact hh
  exact h.2.1.trans (congrArg affinePoint hr)

/-- The actual pole ramification place is the literal infinite projective label. -/
theorem namedSquare_matchedLabel_infty
    (z : ι) (f : RatFunc E) (hf : eF RatFunc.X = f)
    (hvalue : (rationalConfigurationBoundaryPlace k E s (L z)).val.ord f < 0) :
    (τ z).val = (infinityPoint : Projectivization E (E × E)) := by
  have h := namedSquare_matchedLabel_infty_place
    k E s p eF hplaces t ht τ L hcomm z f hf hvalue
  have hz : (τ z).val.rep.2 = 0 := by
    by_contra hn
    have hh : RationalFunctionField.placeOfPoint E
        ((τ z).val.rep.1 / (τ z).val.rep.2) = RationalFunctionField.placeInfty E := by
      simpa only [projectiveRatFuncPlace, ite_eq_right hn] using h
    exact (RationalFunctionField.placeOfPoint_ne_placeInfty E _) hh
  calc
    (τ z).val = Projectivization.mk E (τ z).val.rep (τ z).val.rep_nonzero :=
      (τ z).val.mk_rep.symm
    _ = infinityPoint := by
      apply (Projectivization.mk_eq_mk_iff' E _ _ _ _).mpr
      refine ⟨(τ z).val.rep.1, ?_⟩
      apply Prod.ext
      · exact mul_one _
      · change (τ z).val.rep.1 * 0 = (τ z).val.rep.2
        rw [mul_zero, hz]


/-- Evaluate the cross ratio of the actual four τ-images. The ramification
labels, reference lift, and comparison lift are all retained literally. -/
theorem namedSquare_matchedLabel_crossRatio_sq
    (zA zB z₀ z : ι) (f : RatFunc E) (hf : eF RatFunc.X = f)
    (a₀ a r₀ r : E) (hr₀ : r₀ ^ 2 = a₀) (hr : r ^ 2 = a)
    (hzero : (rationalConfigurationBoundaryPlace k E s (L zA)).val.HasValue f 0)
    (hpole : (rationalConfigurationBoundaryPlace k E s (L zB)).val.ord f < 0)
    (hvalue₀ : (rationalConfigurationBoundaryPlace k E s (L z₀)).val.HasValue f a₀)
    (hvalue : (rationalConfigurationBoundaryPlace k E s (L z)).val.HasValue f a) :
    (crossRatio (τ zA).val (τ zB).val (τ z₀).val (τ z).val) ^ 2 = a / a₀ := by
  have hA := namedSquare_matchedLabel_zero
    k E s p eF hplaces t ht τ L hcomm zA f hf hzero
  have hB := namedSquare_matchedLabel_infty
    k E s p eF hplaces t ht τ L hcomm zB f hf hpole
  have h₀ := namedSquare_matchedLabel_actual_root_coordinate
    k E s p eF hplaces t ht τ L hcomm z₀ f hf a₀ r₀ hr₀ hvalue₀
  have h := namedSquare_matchedLabel_actual_root_coordinate
    k E s p eF hplaces t ht τ L hcomm z f hf a r hr hvalue
  calc
    (crossRatio (τ zA).val (τ zB).val (τ z₀).val (τ z).val) ^ 2 =
        (((τ z).val.rep.1 / (τ z).val.rep.2) /
          ((τ z₀).val.rep.1 / (τ z₀).val.rep.2)) ^ 2 := by
      conv_lhs => rw [hA, hB, h₀.2.1, h.2.1, crossRatio_standard_root_coordinate]
    _ = a / a₀ := namedSquare_matchedLabel_actual_root_ratio
      k E s p eF hplaces t ht τ L hcomm z₀ z f hf a₀ a r₀ r hr₀ hr hvalue₀ hvalue

end Named
end AnabelianGeometry.WeightFiltration
