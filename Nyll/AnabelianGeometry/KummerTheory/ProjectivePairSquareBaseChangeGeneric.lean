/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.KummerTheory.RatFuncPairSquareCoefficientMap
import Nyll.SchemeTheory.FunctionFields.OpenChartGenericPoints
import Nyll.AlgebraicCurves.Models.Charts.OpenChartGenericPoints

/-! # The unchanged square-map generic triangle after actual base change

The two projections of the actual projective base-change square determine the
map. Its generic triangle follows from the same coefficient-compatible pair
square homomorphisms, without a dominance premise or a new coordinate choice.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open AnabelianGeometry.KummerTheory
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
attribute [local instance] CurveModel.isIntegral

namespace AlgebraicGeometry.ProjSpace

/-- The generic-stalk equation of the original finite-map construction is
also the literal RatFunc chart-point equation. -/
theorem ratFuncModel_chartPoint_square_of_generic
    (k : Type) [Field k]
    (φ : RatFunc k →ₐ[k] RatFunc k)
    (p : (projectiveLineRatFuncModel k).C ⟶ (projectiveLineRatFuncModel k).C)
    (hgeneric :
      (projectiveLineRatFuncModel k).C.fromSpecStalk
          (genericPoint (projectiveLineRatFuncModel k).C) ≫ p =
        Spec.map (CommRingCat.ofHom ((projectiveLineRatFuncModel k).ffEquiv.toRingHom.comp
          (φ.toRingHom.comp (projectiveLineRatFuncModel k).ffEquiv.symm.toRingHom))) ≫
          (projectiveLineRatFuncModel k).C.fromSpecStalk
            (genericPoint (projectiveLineRatFuncModel k).C)) :
    (projectiveLineRatFuncModel k).C.functionFieldChartPoint
        (projectiveLineRatFuncModel k).ffEquiv ≫ p =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectiveLineRatFuncModel k).C.functionFieldChartPoint
          (projectiveLineRatFuncModel k).ffEquiv := by
  let M : CurveModel k (RatFunc k) := projectiveLineRatFuncModel k
  have hcancel : M.ffEquiv.symm.toRingHom.comp
      (M.ffEquiv.toRingHom.comp (φ.toRingHom.comp M.ffEquiv.symm.toRingHom)) =
        φ.toRingHom.comp M.ffEquiv.symm.toRingHom := by
    ext z
    exact M.ffEquiv.symm_apply_apply _
  change (Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫
    M.C.fromSpecStalk (genericPoint M.C)) ≫ p =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫
          M.C.fromSpecStalk (genericPoint M.C))
  rw [Category.assoc, hgeneric, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcancel,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

/-- Any map with the two actual base-change projection equations has the
same retained pair-square generic triangle over E. Those projection equations
are supplied by the canonical projective pullback construction. -/
theorem projectivePairSquare_baseChange_generic_square
    (k E : Type) [Field k] [Field E] [Algebra k E]
    (e : RatFunc k ≃ₐ[k] RatFunc k) (eE : RatFunc E ≃ₐ[E] RatFunc E)
    (f : RatFunc k) (he : e RatFunc.X = f)
    (heE : eE RatFunc.X = algebraMap (RatFunc k) (RatFunc E) f)
    (p : (projectiveLineRatFuncModel k).C ⟶ (projectiveLineRatFuncModel k).C)
    (pE : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
    (hpE : pE ≫ map k E 1 = map k E 1 ≫ p)
    (hpEbase : pE ≫ π E 1 = π E 1)
    (hp : (projectiveLineRatFuncModel k).C.functionFieldChartPoint
        (projectiveLineRatFuncModel k).ffEquiv ≫ p =
      Spec.map (CommRingCat.ofHom (ratFuncPairSquareHom e).toRingHom) ≫
        (projectiveLineRatFuncModel k).C.functionFieldChartPoint
          (projectiveLineRatFuncModel k).ffEquiv) :
    (projectiveLineRatFuncModel E).C.functionFieldChartPoint
        (projectiveLineRatFuncModel E).ffEquiv ≫ pE =
      Spec.map (CommRingCat.ofHom (ratFuncPairSquareHom eE).toRingHom) ≫
        (projectiveLineRatFuncModel E).C.functionFieldChartPoint
          (projectiveLineRatFuncModel E).ffEquiv := by
  let qk : Spec (CommRingCat.of (RatFunc k)) ⟶ (projectiveLineRatFuncModel k).C :=
    (projectiveLineRatFuncModel k).C.functionFieldChartPoint
    (projectiveLineRatFuncModel k).ffEquiv
  let qE : Spec (CommRingCat.of (RatFunc E)) ⟶ (projectiveLineRatFuncModel E).C :=
    (projectiveLineRatFuncModel E).C.functionFieldChartPoint
    (projectiveLineRatFuncModel E).ffEquiv
  let a : RatFunc k →+* RatFunc E := algebraMap (RatFunc k) (RatFunc E)
  let φ : RatFunc k →+* RatFunc k := (ratFuncPairSquareHom e).toRingHom
  let φE : RatFunc E →+* RatFunc E := (ratFuncPairSquareHom eE).toRingHom
  let c : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel k).C :=
    map k E 1
  let b : (projectiveLineRatFuncModel E).C ⟶ Spec (CommRingCat.of E) := π E 1
  let sa : Spec (CommRingCat.of (RatFunc E)) ⟶ Spec (CommRingCat.of (RatFunc k)) :=
    Spec.map (CommRingCat.ofHom a)
  let sk : Spec (CommRingCat.of (RatFunc k)) ⟶ Spec (CommRingCat.of (RatFunc k)) :=
    Spec.map (CommRingCat.ofHom φ)
  let sE : Spec (CommRingCat.of (RatFunc E)) ⟶ Spec (CommRingCat.of (RatFunc E)) :=
    Spec.map (CommRingCat.ofHom φE)
  let t : Spec (CommRingCat.of (RatFunc E)) ⟶ Spec (CommRingCat.of E) :=
    Spec.map (CommRingCat.ofHom (algebraMap E (RatFunc E)))
  have hpEc : pE ≫ c = c ≫ p := hpE
  have hpEb : pE ≫ b = b := hpEbase
  have hpk : qk ≫ p = sk ≫ qk := hp
  have hq : qE ≫ c = sa ≫ qk :=
    Scheme.functionFieldChartPoint_comp_of_functionFieldMap
      (C := (projectiveLineRatFuncModel k).C)
      (D := (projectiveLineRatFuncModel E).C)
      (projectiveLineRatFuncModel k).ffEquiv (projectiveLineRatFuncModel E).ffEquiv
      c (projectiveLineMap_denseRange k E) a
      (projectiveLineRatFuncEquiv_coefficientMap k E)
  have hφ : φE.comp a = a.comp φ := by
    ext z
    exact ratFuncPairSquareHom_coefficient_commute e eE f he heE z
  have hSpec : sa ≫ sk = sE ≫ sa := by
    change Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom φE) ≫ Spec.map (CommRingCat.ofHom a)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hφ]
  have hqbase : qE ≫ b = t :=
    CurveModel.functionFieldChartPoint_comp_toBase (projectiveLineRatFuncModel E)
  have hSpecBase : sE ≫ t = t := by
    change Spec.map (CommRingCat.ofHom φE) ≫
      Spec.map (CommRingCat.ofHom (algebraMap E (RatFunc E))) =
        Spec.map (CommRingCat.ofHom (algebraMap E (RatFunc E)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun z : E →+* RatFunc E => Spec.map (CommRingCat.ofHom z))
      (ratFuncPairSquareHom eE).comp_algebraMap
  change qE ≫ pE = sE ≫ qE
  apply (isPullback_map k E 1).hom_ext
  · change (qE ≫ pE) ≫ c = (sE ≫ qE) ≫ c
    exact (Category.assoc qE pE c).trans
      ((congrArg (fun z : (projectiveLineRatFuncModel E).C ⟶
          (projectiveLineRatFuncModel k).C => qE ≫ z) hpEc).trans
      ((Category.assoc qE c p).symm.trans
      ((congrArg (fun z : Spec (CommRingCat.of (RatFunc E)) ⟶
          (projectiveLineRatFuncModel k).C => z ≫ p) hq).trans
      ((Category.assoc sa qk p).trans
      ((congrArg (fun z : Spec (CommRingCat.of (RatFunc k)) ⟶
          (projectiveLineRatFuncModel k).C => sa ≫ z) hpk).trans
      ((Category.assoc sa sk qk).symm.trans
      ((congrArg (fun z : Spec (CommRingCat.of (RatFunc E)) ⟶
          Spec (CommRingCat.of (RatFunc k)) => z ≫ qk) hSpec).trans
      ((Category.assoc sE sa qk).trans
      ((congrArg (fun z : Spec (CommRingCat.of (RatFunc E)) ⟶
          (projectiveLineRatFuncModel k).C => sE ≫ z) hq.symm).trans
        (Category.assoc sE qE c).symm)))))))))
  · change (qE ≫ pE) ≫ b = (sE ≫ qE) ≫ b
    exact (Category.assoc qE pE b).trans
      ((congrArg (fun z : (projectiveLineRatFuncModel E).C ⟶
          Spec (CommRingCat.of E) => qE ≫ z) hpEb).trans
      (hqbase.trans
      (hSpecBase.symm.trans
      ((congrArg (fun z : Spec (CommRingCat.of (RatFunc E)) ⟶
          Spec (CommRingCat.of E) => sE ≫ z) hqbase.symm).trans
        (Category.assoc sE qE b).symm))))

end AlgebraicGeometry.ProjSpace
