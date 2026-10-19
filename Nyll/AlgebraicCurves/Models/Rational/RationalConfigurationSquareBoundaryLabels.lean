/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Models.Rational.RationalSquareModelBoundaryLabels
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineBoundaryPlaces
import Nyll.AlgebraicCurves.Places.Evaluation.RationalPlaceValues

/-! # Literal values supply the actual square-cover boundary labels

The target punctures remain indexed by the original finite configuration after
any constant-field extension. Their actual model places are rational by their
original homogeneous coordinates. Thus their literal evaluations of the same
function supply every finite fibre label, without an additional value or
rationality premise.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
attribute [local instance] Classical.propDecidable



namespace AlgebraicGeometry.ProjSpace

local instance rationalSquareBoundaryChart_isOpenImmersion
    (k E : Type) [Field k] [Field E] [Algebra k E]
    (s : Finset (Projectivization k (k × k))) :
    IsOpenImmersion (show
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) ⟶
          (projectiveLineRatFuncModel E).C from
            rationalConfigurationBaseChangeChart k E s) :=
  rationalConfigurationBaseChangeChart_isOpenImmersion k E s

variable (k E : Type) [Field k] [Field E] [Algebra k E]

/-- Every original puncture remains rational over every extension field,
using the same extended homogeneous representative. -/
theorem rationalConfigurationBoundaryPlace_isRational
    (s : Finset (Projectivization k (k × k))) (a : s) :
    (rationalConfigurationBoundaryPlace k E s a).val.IsRational := by
  change (literalRationalPuncturePlace E (extendedPunctureCoordinates k E a.val)
    (extendedPunctureCoordinates_ne_zero k E a.val)).IsRational
  exact literalRationalPuncturePlace_isRational E _ _

/-- Every actual target boundary place is a pole or has the literal value of
one of the original labels. This works over finite, not necessarily closed, E. -/
theorem rationalConfigurationBoundaryPlaces_actual_values
    (s : Finset (Projectivization k (k × k))) (f : RatFunc E) (hf : f ≠ 0) :
    ∀ V : (projectiveLineRatFuncModel E).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k E s),
      V.val.ord f < 0 ∨ ∃ a : s,
        V.val.HasValue f ((rationalConfigurationBoundaryPlace k E s a).val.evalAt f) := by
  intro V
  obtain ⟨a, rfl⟩ := (rationalConfigurationBoundaryPlaceEquiv k E s).surjective V
  rcases Place.ord_neg_or_hasValue_evalAt
    (rationalConfigurationBoundaryPlace k E s a).val
    (rationalConfigurationBoundaryPlace_isRational k E s a) f hf with h | h
  · exact Or.inl h
  · exact Or.inr ⟨a, h⟩

open AnabelianGeometry.KummerTheory

/-- All actual omitted source places of the square-model open are the
retained finite root labels, their negatives, or infinity. The target values
are proved from the original configuration, not supplied as a premise. -/
theorem rationalConfiguration_squareModel_actual_boundary_labels
    (s : Finset (Projectivization k (k × k)))
    (p : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
    (eF : RatFunc E ≃ₐ[E] RatFunc E) (f : RatFunc E)
    (hf : eF RatFunc.X = f) (hf0 : f ≠ 0)
    (r : s → E)
    (hr : ∀ a, r a ^ 2 =
      (rationalConfigurationBoundaryPlace k E s a).val.evalAt f)
    (hplaces : ∀ y : closedPoints (projectiveLineRatFuncModel E).C,
      ∃ hy : p.base y.val ∈ closedPoints (projectiveLineRatFuncModel E).C,
        (projectiveLineRatFuncModel E).placeOfPoint ⟨p.base y.val, hy⟩ =
          ((projectiveLineRatFuncModel E).placeOfPoint y).restrictAlong
            (ratFuncPairSquareHom eF) (ratFuncPairSquareHom_isIntegral eF)) :
    ∀ W : (projectiveLineRatFuncModel E).openBoundaryPlaces
      (pullback.fst p (rationalConfigurationBaseChangeChart k E s)),
      W.val.IsRational ∧
        (W.val = RationalFunctionField.placeInfty E ∨
          ∃ a : s, W.val = RationalFunctionField.placeOfPoint E (r a) ∨
            W.val = RationalFunctionField.placeOfPoint E (-(r a))) := by
  exact rationalSquareModel_actual_boundary_labels
    (rationalConfigurationBaseChangeChart k E s) p eF f hf
    (fun a => (rationalConfigurationBoundaryPlace k E s a).val.evalAt f)
    r hr hplaces (rationalConfigurationBoundaryPlaces_actual_values k E s f hf0)

end AlgebraicGeometry.ProjSpace
