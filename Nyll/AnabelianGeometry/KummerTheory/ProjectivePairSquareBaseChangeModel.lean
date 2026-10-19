/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.BaseChange.BaseChangedIdentifiedModelIso
import Nyll.AnabelianGeometry.KummerTheory.ProjectivePairSquareBaseChangeGeneric
import Nyll.AlgebraicCurves.Models.FunctionFields.FiniteFlatHomAlgHom

/-! # The original square model, actually base-changed to E

The new map is the universal base change of the already constructed old map.
Its same-function generic triangle identifies it with the finite-flat model
map, giving the actual place restriction formula. The original cover-model
isomorphism is then base-changed by pullback pasting, rather than replacing the
cover with a separately selected normalization.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve TopologicalSpace
open AnabelianGeometry.KummerTheory
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
attribute [local instance] Classical.propDecidable
attribute [local instance] CurveModel.isIntegral

namespace AlgebraicGeometry.ProjSpace

/-- The universal base change of the original square map has the actual
finite-flat model properties and the same RatFunc place restriction formula. -/
theorem projectivePairSquare_baseChangedMap_model_properties
    (k E : Type) [Field k] [Field E] [Algebra k E]
    (e : RatFunc k ≃ₐ[k] RatFunc k) (eE : RatFunc E ≃ₐ[E] RatFunc E)
    (f : RatFunc k) (he : e RatFunc.X = f)
    (heE : eE RatFunc.X = algebraMap (RatFunc k) (RatFunc E) f)
    (p : (projectiveLineRatFuncModel k).C ⟶ (projectiveLineRatFuncModel k).C)
    (hpBase : p ≫ π k 1 = π k 1)
    (hpGeneric : (projectiveLineRatFuncModel k).C.functionFieldChartPoint
        (projectiveLineRatFuncModel k).ffEquiv ≫ p =
      Spec.map (CommRingCat.ofHom (ratFuncPairSquareHom e).toRingHom) ≫
        (projectiveLineRatFuncModel k).C.functionFieldChartPoint
          (projectiveLineRatFuncModel k).ffEquiv) :
    let pE : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C :=
      baseChangedModelMap (isPullback_map k E 1) p hpBase
    IsFinite pE ∧ Flat pE ∧ LocallyOfFinitePresentation pE ∧
      ((projectiveLineRatFuncModel E).C.functionFieldChartPoint
          (projectiveLineRatFuncModel E).ffEquiv ≫ pE =
        Spec.map (CommRingCat.ofHom (ratFuncPairSquareHom eE).toRingHom) ≫
          (projectiveLineRatFuncModel E).C.functionFieldChartPoint
            (projectiveLineRatFuncModel E).ffEquiv) ∧
      ∀ y : closedPoints (projectiveLineRatFuncModel E).C,
        ∃ hy : pE.base y.val ∈ closedPoints (projectiveLineRatFuncModel E).C,
          (projectiveLineRatFuncModel E).placeOfPoint ⟨pE.base y.val, hy⟩ =
            ((projectiveLineRatFuncModel E).placeOfPoint y).restrictAlong
              (ratFuncPairSquareHom eE) (ratFuncPairSquareHom_isIntegral eE) := by
  intro pE
  let M : CurveModel E (RatFunc E) := projectiveLineRatFuncModel E
  have hpEgeneric := projectivePairSquare_baseChange_generic_square k E e eE f he heE p pE
    (baseChangedModelMap_coeff (isPullback_map k E 1) p hpBase)
    (baseChangedModelMap_base (isPullback_map k E 1) p hpBase) hpGeneric
  obtain ⟨p₀, _hbase, hfinite, hflat, hfp, _hrank, hgeneric, hplaces, huniq⟩ :=
    CurveModel.exists_finite_flat_hom_of_algHom M M (ratFuncPairSquareHom eE)
      (ratFuncPairSquareHom_isIntegral eE) (ratFuncPairSquareHom_finite eE)
  have hp₀generic := ratFuncModel_chartPoint_square_of_generic E
    (ratFuncPairSquareHom eE) p₀ hgeneric
  have hpoint : M.C.fromSpecStalk (genericPoint M.C) ≫ pE =
      M.C.fromSpecStalk (genericPoint M.C) ≫ p₀ := by
    let i : Spec (CommRingCat.of (RatFunc E)) ≅
        Spec (CommRingCat.of M.C.functionField) :=
      Scheme.Spec.mapIso M.ffEquiv.symm.toCommRingCatIso.op
    let j : Spec (CommRingCat.of M.C.functionField) ⟶ M.C :=
      M.C.fromSpecStalk (genericPoint M.C)
    have hchart : (i.hom ≫ j) ≫ pE = (i.hom ≫ j) ≫ p₀ :=
      hpEgeneric.trans hp₀generic.symm
    apply (cancel_epi i.hom).mp
    exact (Category.assoc i.hom j pE).symm.trans
      (hchart.trans (Category.assoc i.hom j p₀))
  have heq : pE = p₀ := huniq pE hpoint
  rw [heq]
  exact ⟨hfinite, hflat, hfp, hp₀generic, hplaces⟩

/-- Base change the already identified original named cover to the literal
E-square-model open, retaining both its projection and original model chart. -/
theorem projectivePairSquare_baseChange_original_cover_iso
    (k E : Type) [Field k] [Field E] [Algebra k E]
    (p : (projectiveLineRatFuncModel k).C ⟶ (projectiveLineRatFuncModel k).C)
    (hpBase : p ≫ π k 1 = π k 1)
    {U W UE : Scheme}
    (j : U ⟶ (projectiveLineRatFuncModel k).C) (w : W ⟶ U)
    (J : W ≅ pullback p j) (hJ : J.hom ≫ pullback.snd p j = w)
    (bU : UE ⟶ U) (jE : UE ⟶ (projectiveLineRatFuncModel E).C)
    (hchart : bU ≫ j = jE ≫ map k E 1) :
    let pE : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C :=
      baseChangedModelMap (isPullback_map k E 1) p hpBase
    ∃ JE : pullback w bU ≅ pullback pE jE,
      JE.hom ≫ pullback.snd pE jE = pullback.snd w bU ∧
      JE.hom ≫ pullback.fst pE jE ≫ map k E 1 =
        pullback.fst w bU ≫ J.hom ≫ pullback.fst p j := by
  intro pE
  exact exists_baseChangedIdentifiedModelIso (isPullback_map k E 1) p hpBase
    j w J hJ bU jE hchart

end AlgebraicGeometry.ProjSpace
