/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.FunctionFields.Rational.ProjectiveRatFuncPairEvaluation
import Nyll.AlgebraicCurves.FunctionFields.Constants.RatFuncConstantExtensionOrders
import Nyll.AlgebraicCurves.FunctionFields.Constants.RatFuncRationalPairConstantExtension
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineStandardPlace
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationBoundaryPlaceOrders
import Nyll.AlgebraicCurves.Places.Evaluation.EvalAtMapEqComapEq

/-! # Original arithmetic cusp-value ratios are projective cross ratios

The arithmetic places are exactly the choices used for the original
normalization-prime decompositions. Their values are compared with the actual
geometric places using the proved order-comap equality. The literal projective
model identifies those geometric places with the standard coordinate places.
The result reads the unchanged arithmetic function in the original base field.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AlgebraicGeometry.ProjSpace

open AnabelianGeometry.ProjectiveLine AnabelianGeometry.KummerTheory

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ]

/-- Extend the same original homogeneous coordinates to the geometric constants. -/
def rationalConfigurationProjectivePoint
    (p : Projectivization k (k × k)) : Projectivization κ (κ × κ) :=
  Projectivization.mk κ (extendedPunctureCoordinates k κ p)
    (extendedPunctureCoordinates_ne_zero k κ p)

theorem rationalConfigurationProjectivePoint_actualPoint
    (p : Projectivization k (k × k)) :
    projectiveRationalPoint (rationalConfigurationProjectivePoint k κ p) =
      rationalConfigurationGeometricPoint k κ p :=
  projectiveRationalPoint_mk _ _

theorem rationalConfigurationProjectivePoint_injective :
    Function.Injective (rationalConfigurationProjectivePoint k κ) := by
  intro p q h
  apply rationalConfigurationGeometricPoint_injective k κ
  rw [← rationalConfigurationProjectivePoint_actualPoint k κ p,
    ← rationalConfigurationProjectivePoint_actualPoint k κ q, h]

theorem crossRatio_rationalConfigurationProjectivePoint
    (a b c d : Projectivization k (k × k)) :
    crossRatio (rationalConfigurationProjectivePoint k κ a)
      (rationalConfigurationProjectivePoint k κ b)
      (rationalConfigurationProjectivePoint k κ c)
      (rationalConfigurationProjectivePoint k κ d) = algebraMap k κ (crossRatio a b c d) := by
  simp only [rationalConfigurationProjectivePoint, crossRatio_mk]
  simp only [crossRatio, homogeneousCrossRatio, bracket, extendedPunctureCoordinates,
    map_div₀, map_mul, map_sub]

/-- The actual labelled geometric boundary is the standard place of that
same label in the literal projective-line function-field coordinate. -/
theorem rationalConfigurationBoundaryPlace_eq_projectiveRatFuncPlace
    (s : Finset (Projectivization k (k × k))) (x : s) :
    (rationalConfigurationBoundaryPlace k κ s x).val =
      projectiveRatFuncPlace (rationalConfigurationProjectivePoint k κ x.val) := by
  let M := projectiveLineRatFuncModel κ
  let W := (rationalConfigurationBoundaryPlace k κ s x).val
  let y : closedPoints M.C :=
    ⟨projectiveRationalPoint (rationalConfigurationProjectivePoint k κ x.val),
      isClosed_singleton_rationalPuncturePoint _ _⟩
  have hy : M.placeEquiv.symm W = y := by
    apply Subtype.ext
    change ((projectiveLineRatFuncModel κ).placeEquiv.symm
      (rationalConfigurationBoundaryPlace k κ s x).val).val = _
    rw [rationalConfigurationBoundaryPlace_center,
      ← rationalConfigurationProjectivePoint_actualPoint k κ x.val]
  have hplace : W = M.placeOfPoint y := by
    calc
      W = M.placeEquiv (M.placeEquiv.symm W) := (M.placeEquiv.apply_symm_apply W).symm
      _ = M.placeOfPoint y := congrArg M.placeOfPoint hy
  change W = _
  rw [hplace]
  exact projectiveLineRatFuncModel_placeOfPoint_projectiveRationalPoint κ _

variable [IsAlgClosed κ] [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]

/-- The already chosen pair function gives the original configuration's cross
ratios at the SAME arithmetic places used by cusp-root specialization. -/
theorem rationalConfiguration_pairFunction_chosenValue_ratio_eq_crossRatio
    (s : Finset (Projectivization k (k × k))) (a b c d : s)
    (hcb : c ≠ b) (hdb : d ≠ b)
    (f : RatFunc k) (hf : f ≠ 0)
    (hgeom : ∀ W : Place κ (RatFunc κ),
      W.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
        (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
        (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0)) :
    let V : s → Place k (RatFunc k) := fun x =>
      (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s
        (rationalConfigurationBoundaryPlace k κ s x)).choose
    (V d).evalAt f / (V c).evalAt f = crossRatio a.val b.val c.val d.val := by
  intro V
  have hV (x : s) : (V x).IsRational :=
    (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s
      (rationalConfigurationBoundaryPlace k κ s x)).choose_spec.1
  have hord (x : s) : ∀ z : RatFunc k,
      (rationalConfigurationBoundaryPlace k κ s x).val.ord
        (algebraMap (RatFunc k) (RatFunc κ) z) = (V x).ord z :=
    (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s
      (rationalConfigurationBoundaryPlace k κ s x)).choose_spec.2
  have heval (x : s) (hxb : x ≠ b) :
      (rationalConfigurationBoundaryPlace k κ s x).val.evalAt
        (algebraMap (RatFunc k) (RatFunc κ) f) = algebraMap k κ ((V x).evalAt f) := by
    apply Place.evalAt_map_eq_of_comap_eq (algebraMap k κ)
      (algebraMap (RatFunc k) (RatFunc κ))
      (fun z => (IsScalarTower.algebraMap_apply k (RatFunc k) (RatFunc κ) z).symm.trans
        (IsScalarTower.algebraMap_apply k κ (RatFunc κ) z))
      (V x) (rationalConfigurationBoundaryPlace k κ s x).val
      (ratFunc_constantExtension_comap_eq_of_ord_eq (V x)
        (rationalConfigurationBoundaryPlace k κ s x).val (hord x)) (hV x)
    apply (V x).mem_of_ord_nonneg hf
    have hWb : (rationalConfigurationBoundaryPlace k κ s x).val ≠
        (rationalConfigurationBoundaryPlace k κ s b).val := by
      intro h
      exact hxb ((rationalConfigurationBoundaryPlaceEquiv k κ s).injective (Subtype.ext h))
    rw [← hord x f, hgeom, ite_eq_right hWb, sub_zero]
    split_ifs <;> omega
  apply (algebraMap k κ).injective
  rw [map_div₀, ← heval d hdb, ← heval c hcb]
  simp only [rationalConfigurationBoundaryPlace_eq_projectiveRatFuncPlace]
  apply (ratFunc_pair_evalAt_ratio_eq_crossRatio
    (rationalConfigurationProjectivePoint k κ a.val)
    (rationalConfigurationProjectivePoint k κ b.val)
    (rationalConfigurationProjectivePoint k κ c.val)
    (rationalConfigurationProjectivePoint k κ d.val)
    ((rationalConfigurationProjectivePoint_injective k κ).ne (Subtype.coe_injective.ne hcb))
    ((rationalConfigurationProjectivePoint_injective k κ).ne (Subtype.coe_injective.ne hdb))
    (algebraMap (RatFunc k) (RatFunc κ) f) ((map_ne_zero _).mpr hf) ?_).trans
    (crossRatio_rationalConfigurationProjectivePoint k κ a.val b.val c.val d.val)
  intro W
  simpa only [rationalConfigurationBoundaryPlace_eq_projectiveRatFuncPlace] using hgeom W

end AlgebraicGeometry.ProjSpace
