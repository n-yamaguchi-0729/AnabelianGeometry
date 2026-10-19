/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineStandardPlace
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineRatFuncBaseChange
import Nyll.SchemeTheory.ProjectiveSpace.ProjectiveLineRatFuncBaseChange
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineBoundaryPlaces
import Nyll.AlgebraicCurves.Models.Sections.RationalSectionBoundaryPlace
import Nyll.AlgebraicCurves.Places.Evaluation.PlaceValueAlongOrders

/-! # The original rational values over an algebraic separable constant extension

The map is the literal coefficient extension on the original rational-function
fields. Stalk functoriality at the same projective rational point supplies the
valuation-ring inclusion. Unramified constant extension then supplies all
normalized orders and the unchanged residue value. The extension need not be
algebraically closed, so this applies directly to the selected finite field.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AlgebraicGeometry.ProjSpace

variable (k E : Type) [Field k] [Field E] [Algebra k E]
  [Algebra.IsAlgebraic k E] [Algebra.IsSeparable k E]

/-- Every original rational label has the same normalized orders in the
literal model after the actual separable algebraic coefficient extension. -/
theorem rationalConfigurationBoundaryPlace_coefficient_orders
    (s : Finset (Projectivization k (k × k))) (a : s) :
    ∀ f : RatFunc k,
      (rationalConfigurationBoundaryPlace k E s a).val.ord
        (algebraMap (RatFunc k) (RatFunc E) f) =
      (literalRationalPuncturePlace k a.val.rep a.val.rep_nonzero).ord f := by
  let M₀ := projectiveLineRatFuncModel k
  let M := projectiveLineRatFuncModel E
  let y : closedPoints M.C :=
    ⟨rationalConfigurationGeometricPoint k E a.val,
      rationalConfigurationGeometricPoint_isClosed k E a.val⟩
  have hcenter : map k E 1 y.val = projectiveRationalPoint a.val :=
    map_rationalConfigurationGeometricPoint k E a.val
  have hclosed : IsClosed ({map k E 1 y.val} : Set M₀.C) := by
    rw [hcenter]
    exact isClosed_singleton_rationalPuncturePoint a.val.rep a.val.rep_nonzero
  have hinclusion := M₀.placeOfPoint_le_comap_of_functionFieldMap M
    (map k E 1) (projectiveLineMap_denseRange k E)
    (projectiveLineRatFuncEquiv_coefficientMap k E) y hclosed
  have horders := CurveModel.ratFunc_ord_eq_of_place_le_comap
    (M₀.placeOfPoint ⟨map k E 1 y.val, hclosed⟩) (M.placeOfPoint y) hinclusion
  have hpoint : (⟨map k E 1 y.val, hclosed⟩ : closedPoints M₀.C) =
      ⟨projectiveRationalPoint a.val,
        isClosed_singleton_rationalPuncturePoint a.val.rep a.val.rep_nonzero⟩ :=
    Subtype.ext hcenter
  rw [hpoint] at horders
  exact horders

/-- The value at the extended original label is the image of the value at
its original literal k-place. This includes the zero convention at poles. -/
theorem rationalConfigurationBoundaryPlace_coefficient_evalAt
    (s : Finset (Projectivization k (k × k))) (a : s)
    (f : RatFunc k) (hf : f ≠ 0) :
    (rationalConfigurationBoundaryPlace k E s a).val.evalAt
        (algebraMap (RatFunc k) (RatFunc E) f) =
      algebraMap k E
        ((literalRationalPuncturePlace k a.val.rep a.val.rep_nonzero).evalAt f) := by
  have hW : (rationalConfigurationBoundaryPlace k E s a).val.IsRational := by
    change (literalRationalPuncturePlace E (extendedPunctureCoordinates k E a.val)
      (extendedPunctureCoordinates_ne_zero k E a.val)).IsRational
    exact literalRationalPuncturePlace_isRational E _ _
  exact Place.evalAt_eq_of_orderCompatible
    (algebraMap (RatFunc k) (RatFunc E))
    (fun c => (IsScalarTower.algebraMap_apply k (RatFunc k) (RatFunc E) c).symm.trans
      (IsScalarTower.algebraMap_apply k E (RatFunc E) c))
    (literalRationalPuncturePlace k a.val.rep a.val.rep_nonzero)
    (rationalConfigurationBoundaryPlace k E s a).val
    (literalRationalPuncturePlace_isRational k _ _) hW
    (rationalConfigurationBoundaryPlace_coefficient_orders k E s a) f hf

/-- The same selected finite-field root labels have the actual extended
boundary values, without another choice of values or square roots. -/
theorem rationalConfigurationBoundaryPlace_coefficient_square_values
    (s : Finset (Projectivization k (k × k)))
    (f : RatFunc k) (hf : f ≠ 0) (r : s → E)
    (hr : ∀ a, r a ^ 2 = algebraMap k E
      ((literalRationalPuncturePlace k a.val.rep a.val.rep_nonzero).evalAt f)) :
    ∀ a, r a ^ 2 = (rationalConfigurationBoundaryPlace k E s a).val.evalAt
      (algebraMap (RatFunc k) (RatFunc E) f) := by
  intro a
  exact (hr a).trans (rationalConfigurationBoundaryPlace_coefficient_evalAt
    k E s a f hf).symm

end AlgebraicGeometry.ProjSpace
