/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineBaseChange
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareBoundaryProjection
import Nyll.AlgebraicCurves.Models.Rational.RationalBoundaryConfigurationIso
import Nyll.AlgebraicCurves.Places.Restriction.RestrictAlongSurjective
import Nyll.AlgebraicCurves.Places.Evaluation.PlaceValueRestrictAlong
import Nyll.AnabelianGeometry.KummerTheory.RatFuncCoordinatePlaceUniqueness
import Nyll.AnabelianGeometry.KummerTheory.RationalSquareBoundaryLabelConverse
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticBoundaryFiniteLabels

/-! # Named Square Selected Labels -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace AnabelianGeometry.ProjectiveLine
open AnabelianGeometry.KummerTheory
attribute [local instance] Classical.propDecidable
  MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AnabelianGeometry.WeightFiltration

private theorem separableAlong_of_finite_charZero
    {K F L : Type} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [CharZero F]
    (φ : F →ₐ[K] L) (hfin : FiniteAlong K φ) : SeparableAlong K φ := by
  let : Algebra F L := algebraAlong φ
  have : Module.Finite F L := hfin
  exact Algebra.IsSeparable.of_integral F L

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
variable (S : Finset (Projectivization E (E × E)))
variable (hS : ∀ z, z ∈ S ↔ projectiveRationalPoint z ∉ Set.range
  (pullback.fst p (rationalConfigurationBaseChangeChart k E s)))
local notation "pS" =>
  namedSquareOriginalLabelProjection k E s p eF hplaces S hS

theorem namedSquare_exists_label_of_rational_place
    (c : s) (W : Place E (RatFunc E)) (hW : W.IsRational)
    (hrestrict : W.restrictAlong (ratFuncPairSquareHom eF)
      (ratFuncPairSquareHom_isIntegral eF) =
        (rationalConfigurationBoundaryPlace k E s c).val) :
    ∃ z : S, projectiveRatFuncPlace z.val = W ∧ pS z = c := by
  let M := projectiveLineRatFuncModel E
  let j : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1)) ⟶ M.C :=
    rationalConfigurationBaseChangeChart k E s
  have : IsOpenImmersion j := rationalConfigurationBaseChangeChart_isOpenImmersion k E s
  have hWb : W ∈ M.openBoundaryPlaces (pullback.fst p j) := by
    apply (CurveModel.openBoundaryPlaces_pullback_iff_restrictAlong M M p
      (ratFuncPairSquareHom eF) (ratFuncPairSquareHom_isIntegral eF) hplaces j W).mpr
    rw [hrestrict]
    exact (rationalConfigurationBoundaryPlace k E s c).property
  obtain ⟨z, hz⟩ := exists_projectiveRationalPoint_of_isRational E W hW
  have hcenter : (M.placeEquiv.symm W).val = projectiveRationalPoint z := by
    have h := congrArg M.placeEquiv.symm hz
    rw [← M.placeEquiv_apply, M.placeEquiv.symm_apply_apply] at h
    exact (congrArg Subtype.val h).symm
  have hzS : z ∈ S := by
    apply (hS z).mpr
    rw [← hcenter]
    exact hWb
  have hplace : projectiveRatFuncPlace z = W := by
    have h := projectiveLineRatFuncModel_placeOfPoint_projectiveRationalPoint E z
    exact h.symm.trans hz
  refine ⟨⟨z, hzS⟩, hplace, ?_⟩
  apply (rationalConfigurationBoundaryPlaceEquiv k E s).injective
  apply Subtype.ext
  exact (namedSquareOriginalLabelProjection_place k E s p eF hplaces S hS
    ⟨z, hzS⟩).trans ((congrArg (fun V : Place E (RatFunc E) =>
      V.restrictAlong (ratFuncPairSquareHom eF) (ratFuncPairSquareHom_isIntegral eF))
      hplace).trans hrestrict)

theorem namedSquare_exists_label_of_selected_root
    (c : s) (f : RatFunc E) (hf : eF RatFunc.X = f)
    (a r : E) (hr : r ^ 2 = a)
    (hvalue : (rationalConfigurationBoundaryPlace k E s c).val.HasValue f a) :
    ∃ z : S, projectiveRatFuncPlace z.val = RationalFunctionField.placeOfPoint E r ∧
      pS z = c := by
  have hrat : (RationalFunctionField.placeOfPoint E r).IsRational := by
    apply (Place.isRational_iff_deg_eq_one _).mpr
    exact RationalFunctionField.deg_placeOfPoint E r
  exact namedSquare_exists_label_of_rational_place k E s p eF hplaces S hS c
    (RationalFunctionField.placeOfPoint E r) hrat
    (ratFuncPairSquare_restrict_placeOfPoint_root eF f hf _ a r hr hvalue)

theorem namedSquare_exists_label_of_pole [CharZero E]
    (b : s) (f : RatFunc E) (hf : eF RatFunc.X = f)
    (hpole : (rationalConfigurationBoundaryPlace k E s b).val.ord f < 0) :
    ∃ z : S, projectiveRatFuncPlace z.val = RationalFunctionField.placeInfty E ∧
      pS z = b := by
  let φ : RatFunc E →ₐ[E] RatFunc E := ratFuncPairSquareHom eF
  have hφ : φ.toRingHom.IsIntegral := ratFuncPairSquareHom_isIntegral eF
  have hfin : FiniteAlong E φ := ratFuncPairSquareHom_finite eF
  have hsep : SeparableAlong E φ := separableAlong_of_finite_charZero φ hfin
  obtain ⟨W, hW⟩ := Place.restrictAlong_surjective φ hφ hfin hsep
    (rationalConfigurationBoundaryPlace k E s b).val
  have hneg := Place.ord_neg_of_restrictAlong_eq φ hφ W
    (rationalConfigurationBoundaryPlace k E s b).val hW f hpole
  change W.ord (ratFuncPairSquareHom eF f) < 0 at hneg
  rw [ratFuncPairSquareHom_apply_pair eF f hf] at hneg
  have hWI := ratFunc_eq_placeInfty_of_square_ord_neg W hneg
  have hrestrict : (RationalFunctionField.placeInfty E).restrictAlong φ hφ =
      (rationalConfigurationBoundaryPlace k E s b).val := by
    exact (congrArg (fun V : Place E (RatFunc E) => V.restrictAlong φ hφ)
      hWI.symm).trans hW
  have hrat : (RationalFunctionField.placeInfty E).IsRational := by
    apply (Place.isRational_iff_deg_eq_one _).mpr
    exact RationalFunctionField.deg_placeInfty E
  exact namedSquare_exists_label_of_rational_place k E s p eF hplaces S hS b
    (RationalFunctionField.placeInfty E) hrat hrestrict

end Named
end AnabelianGeometry.WeightFiltration
