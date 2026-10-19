/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.ProjectiveSpace.ProjectiveLinePolynomialChartBaseChange
import Nyll.SchemeTheory.FunctionFields.AffineFunctionFieldNaturality
import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality

/-! # The literal rational coordinate under extension of constants

The chart square is proved by the preceding
module from the actual homogeneous coefficient map. All density proofs
and the equality with the standard RatFunc coefficient extension are
constructed here. No function-field comparison is assumed.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open EtaleFundamentalGroups
open scoped RatFunc

local instance projectiveLineBaseChangeAffineFunctionFieldAlgebra
    (R : Type) [CommRing R] [IsDomain R] :
    Algebra R (Spec (CommRingCat.of R)).functionField :=
  RingHom.toAlgebra
    ((StructureSheaf.toStalk R
        (show PrimeSpectrum.Top R from genericPoint (Spec (CommRingCat.of R)))) :
      CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).functionField).hom

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

/-- Equal scheme maps induce equal function-field maps with any density witnesses. -/
theorem functionFieldMap_eq_of_eq
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f g : Y ⟶ X) (hf : DenseRange f) (hg : DenseRange g) (h : f = g) :
    f.functionFieldMap hf = g.functionFieldMap hg := by
  subst g
  rfl

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ]

local instance projectiveLineBaseChange_integral (F : Type) [Field F] :
    IsIntegral (Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) F)) :=
  projectiveSpace_isIntegral F 1

/-- Density of the actual coefficient map on affine polynomial charts. -/
theorem polynomialCoefficientSpecMap_denseRange :
    DenseRange (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k κ)))) :=
  Scheme.Hom.affineSpecMap_denseRange_of_injective
    (Polynomial.mapRingHom (algebraMap k κ))
    (Polynomial.map_injective _ (algebraMap k κ).injective)

/-- The actual coefficient map on Proj is dense, as detected on chart 1. -/
theorem projectiveLineMap_denseRange : DenseRange (map k κ 1) := by
  have hj : DenseRange (projectiveLinePolynomialChart k) :=
    (projectiveLinePolynomialChart k).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace
      (projectiveLinePolynomialChart k)
  have h : DenseRange (projectiveLinePolynomialChart κ ≫ map k κ 1) := by
    rw [projectiveLinePolynomialChart_comp_map]
    exact hj.comp (polynomialCoefficientSpecMap_denseRange k κ)
      (projectiveLinePolynomialChart k).continuous
  exact DenseRange.of_comp
    (f := (map k κ 1 : _ → _))
    (g := (projectiveLinePolynomialChart κ : _ → _)) h

/-- The standard fraction-field coefficient embedding on a polynomial. -/
theorem ratFuncCoefficientMap_polynomial (p : Polynomial k) :
    algebraMap (RatFunc k) (RatFunc κ) (algebraMap (Polynomial k) (RatFunc k) p) =
      algebraMap (Polynomial κ) (RatFunc κ) (p.map (algebraMap k κ)) := by
  rw [← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) (RatFunc κ),
    RatFunc.algebraMap_apply]
  simp only [map_one, div_one]
  rfl

/-- Naturality of the canonical polynomial fraction-field equivalences. -/
theorem polynomialFunctionFieldEquiv_coefficientMap (z : RatFunc k) :
    Scheme.Hom.functionFieldMap
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k κ))))
        (polynomialCoefficientSpecMap_denseRange k κ)
        (polynomialFunctionFieldEquiv k z) =
      polynomialFunctionFieldEquiv κ (algebraMap (RatFunc k) (RatFunc κ) z) := by
  have hp : ∀ p : Polynomial k,
      Scheme.Hom.functionFieldMap
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k κ))))
          (polynomialCoefficientSpecMap_denseRange k κ)
          (polynomialFunctionFieldEquiv k (algebraMap (Polynomial k) (RatFunc k) p)) =
        polynomialFunctionFieldEquiv κ
          (algebraMap (RatFunc k) (RatFunc κ)
            (algebraMap (Polynomial k) (RatFunc k) p)) := by
    intro p
    rw [AlgEquiv.commutes, ratFuncCoefficientMap_polynomial, AlgEquiv.commutes]
    exact Scheme.Hom.affineSpecMap_functionFieldMap_algebraMap
      (Polynomial.mapRingHom (algebraMap k κ))
      (polynomialCoefficientSpecMap_denseRange k κ) p
  induction z using RatFunc.induction_on with
  | f p q _hq =>
    simp only [map_div₀, hp]

/-- The explicit x0/x1 identification intertwines the actual projective
coefficient map with the standard extension k(t) → κ(t). -/
theorem projectiveLineRatFuncEquiv_coefficientMap (z : RatFunc k) :
    (map k κ 1).functionFieldMap (projectiveLineMap_denseRange k κ)
        (projectiveLineRatFuncEquiv k z) =
      projectiveLineRatFuncEquiv κ (algebraMap (RatFunc k) (RatFunc κ) z) := by
  let jk := projectiveLinePolynomialChart k
  let jκ := projectiveLinePolynomialChart κ
  let f := Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k κ)))
  have hjk : DenseRange jk :=
    jk.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace jk
  have hjκ : DenseRange jκ :=
    jκ.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace jκ
  have hf : DenseRange f := polynomialCoefficientSpecMap_denseRange k κ
  have hmap := projectiveLineMap_denseRange k κ
  have hsquare : jκ ≫ map k κ 1 = f ≫ jk :=
    projectiveLinePolynomialChart_comp_map k κ
  have hcomp : (jκ.functionFieldMap hjκ).comp ((map k κ 1).functionFieldMap hmap) =
      (f.functionFieldMap hf).comp (jk.functionFieldMap hjk) := by
    calc
      _ = (jκ ≫ map k κ 1).functionFieldMap (hmap.comp hjκ (map k κ 1).continuous) :=
        functionFieldMap_comp_of_dense (map k κ 1) hmap jκ hjκ
      _ = (f ≫ jk).functionFieldMap (hjk.comp hf jk.continuous) :=
        functionFieldMap_eq_of_eq _ _ _ _ hsquare
      _ = _ := (functionFieldMap_comp_of_dense jk hjk f hf).symm
  apply jκ.functionFieldRingEquivOfIsOpenImmersion.injective
  have h := DFunLike.congr_fun hcomp (projectiveLineRatFuncEquiv k z)
  change jκ.functionFieldRingEquivOfIsOpenImmersion
      ((map k κ 1).functionFieldMap hmap (projectiveLineRatFuncEquiv k z)) =
    f.functionFieldMap hf
      (jk.functionFieldRingEquivOfIsOpenImmersion (projectiveLineRatFuncEquiv k z)) at h
  have hk : jk.functionFieldRingEquivOfIsOpenImmersion
      (projectiveLineRatFuncEquiv k z) = polynomialFunctionFieldEquiv k z := by
    exact jk.functionFieldRingEquivOfIsOpenImmersion.apply_symm_apply _
  have hκ : jκ.functionFieldRingEquivOfIsOpenImmersion
      (projectiveLineRatFuncEquiv κ (algebraMap (RatFunc k) (RatFunc κ) z)) =
    polynomialFunctionFieldEquiv κ (algebraMap (RatFunc k) (RatFunc κ) z) := by
    exact jκ.functionFieldRingEquivOfIsOpenImmersion.apply_symm_apply _
  rw [hκ]
  rw [hk] at h
  exact h.trans (polynomialFunctionFieldEquiv_coefficientMap k κ z)

/-- Density for the literal pullback comparison used in the arithmetic
boundary-equivariance theorem. -/
theorem projectiveLineBaseChangeProjection_denseRange :
    DenseRange ((isPullback_map k κ 1).isoPullback.hom ≫
      CategoryTheory.Limits.pullback.fst (π k 1)
        (Spec.map (CommRingCat.ofHom (algebraMap k κ)))) := by
  rw [(isPullback_map k κ 1).isoPullback_hom_fst]
  exact projectiveLineMap_denseRange k κ

end AlgebraicGeometry.ProjSpace
