/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationPairFunction
import Nyll.AlgebraicCurves.FunctionFields.Constants.RatFuncRationalPairConstantExtension
import Nyll.AlgebraicCurves.Places.Basic

/-! # Arithmetic and geometric Kummer units of the same pair function

The original rational places
are identified with actual omitted arithmetic closed points, and both
order formulas returned by the pair-function construction are retained.
One function is chosen before all exponents; no later function is selected.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AlgebraicGeometry.ProjSpace

open AnabelianGeometry.KummerTheory

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
  [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]

omit [IsAlgClosed κ] in
/-- Any arithmetic place with the known normalized orders at the specified
geometric puncture is the actual omitted arithmetic place of that label. -/
theorem rationalConfigurationBoundaryPlace_rationalPlace_mem_openBoundaryPlaces
    (s : Finset (Projectivization k (k × k))) (a : s)
    (V : Place k (RatFunc k))
    (hord : ∀ z : RatFunc k,
      (rationalConfigurationBoundaryPlace k κ s a).val.ord
        (algebraMap (RatFunc k) (RatFunc κ) z) = V.ord z) :
    V ∈ (projectiveLineRatFuncModel k).openBoundaryPlaces
      (rationalConfigurationOpen s).ι := by
  let M₀ := projectiveLineRatFuncModel k
  let M := projectiveLineRatFuncModel κ
  let W := (rationalConfigurationBoundaryPlace k κ s a).val
  let y : closedPoints M.C := M.placeEquiv.symm W
  have hcenter : map k κ 1 y.val = projectiveRationalPoint a.val := by
    change map k κ 1
      ((projectiveLineRatFuncModel κ).placeEquiv.symm
        (rationalConfigurationBoundaryPlace k κ s a).val).val = _
    rw [rationalConfigurationBoundaryPlace_center,
      map_rationalConfigurationGeometricPoint]
  have hclosed : IsClosed ({map k κ 1 y.val} : Set M₀.C) := by
    rw [hcenter]
    exact isClosed_singleton_rationalPuncturePoint a.val.rep a.val.rep_nonzero
  let x : closedPoints M₀.C := ⟨map k κ 1 y.val, hclosed⟩
  have hyplace : M.placeOfPoint y = W := by
    change M.placeEquiv (M.placeEquiv.symm W) = W
    exact M.placeEquiv.apply_symm_apply W
  have horders : ∀ z : RatFunc k,
      W.ord (algebraMap (RatFunc k) (RatFunc κ) z) =
        (M₀.placeOfPoint x).ord z := by
    intro z
    rw [← hyplace]
    exact CurveModel.ratFunc_ord_eq_of_place_le_comap
      (M₀.placeOfPoint x) (M.placeOfPoint y)
      (M₀.placeOfPoint_le_comap_of_functionFieldMap M
        (map k κ 1) (projectiveLineMap_denseRange k κ)
        (projectiveLineRatFuncEquiv_coefficientMap k κ) y hclosed) z
  have hV : V = M₀.placeOfPoint x := by
    apply Place.ext
    ext z
    rcases eq_or_ne z 0 with rfl | hz
    · exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [V.mem_iff_ord_nonneg hz, (M₀.placeOfPoint x).mem_iff_ord_nonneg hz,
        ← hord z, ← horders z]
  rw [hV]
  change (M₀.placeEquiv.symm (M₀.placeOfPoint x)).val ∉
    Set.range (rationalConfigurationOpen s).ι
  rw [← M₀.placeEquiv_apply, M₀.placeEquiv.symm_apply_apply]
  rintro ⟨u, hu⟩
  have hne := (mem_rationalConfigurationOpen_iff s u.val).mp u.property
    a.val a.property
  exact hne (hu.trans hcenter)

/-- Retain the arithmetic divisor and prove its support is contained in the
actual arithmetic boundary, together with the full geometric divisor. -/
theorem rationalConfiguration_exists_pair_function_with_arithmetic_boundary
    (s : Finset (Projectivization k (k × k))) (a b : s) :
    ∃ V₀ Vinf : (projectiveLineRatFuncModel k).openBoundaryPlaces
        (rationalConfigurationOpen s).ι,
    ∃ f : RatFunc k, f ≠ 0 ∧
      (∀ V : Place k (RatFunc k),
        V.ord f = (if V = V₀.val then 1 else 0) -
          (if V = Vinf.val then 1 else 0)) ∧
      ∀ W : Place κ (RatFunc κ),
        W.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
          (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
          (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0) := by
  obtain ⟨V₀, hV₀, hord₀⟩ :=
    rationalConfigurationBoundaryPlace_exists_rationalPlace k κ s a
  obtain ⟨Vinf, hVinf, hordinf⟩ :=
    rationalConfigurationBoundaryPlace_exists_rationalPlace k κ s b
  have hb₀ := rationalConfigurationBoundaryPlace_rationalPlace_mem_openBoundaryPlaces
    k κ s a V₀ hord₀
  have hbinf := rationalConfigurationBoundaryPlace_rationalPlace_mem_openBoundaryPlaces
    k κ s b Vinf hordinf
  obtain ⟨f, hf, harith, hgeom⟩ :=
    ratFunc_exists_function_geometric_rationalPlace_pair V₀ Vinf hV₀ hVinf
      (rationalConfigurationBoundaryPlace k κ s a).val
      (rationalConfigurationBoundaryPlace k κ s b).val hord₀ hordinf
  exact ⟨⟨V₀, hb₀⟩, ⟨Vinf, hbinf⟩, f, hf, harith, hgeom⟩

end AlgebraicGeometry.ProjSpace
