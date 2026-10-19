/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineAmbientFields
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineGenericPoints

/-! # Rational Configuration Matched Ambient Action -/

noncomputable section
open scoped Polynomial RatFunc
open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.ProjSpace

namespace AnabelianGeometry.WeightFiltration

theorem ambientRingHom_eq_of_functionFieldChartPoint
    {F Ω : Type} [Field F] [Field Ω]
    (X : Scheme) [IsIntegral X] (e : F ≃+* X.functionField)
    (a b : F →+* Ω)
    (h : Spec.map (CommRingCat.ofHom a) ≫ X.functionFieldChartPoint e =
      Spec.map (CommRingCat.ofHom b) ≫ X.functionFieldChartPoint e) :
    a = b := by
  have hc : a.comp e.symm.toRingHom = b.comp e.symm.toRingHom := by
    have hcat : CommRingCat.ofHom (a.comp e.symm.toRingHom) =
        CommRingCat.ofHom (b.comp e.symm.toRingHom) := by
      apply Spec.map_injective
      apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
      simpa only [Scheme.functionFieldChartPoint, ← Category.assoc,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp] using h
    exact congrArg CommRingCat.Hom.hom hcat
  ext t
  have ht := RingHom.congr_fun hc (e t)
  change a (e.symm (e t)) = b (e.symm (e t)) at ht
  simpa only [RingEquiv.symm_apply_apply] using ht

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

theorem rationalConfiguration_matchedAmbient_arithmeticMap_eq
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [Infinite k]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω]
    [Algebra (rationalConfigurationOpen s : Scheme).functionField Ω]
    [Algebra (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField Ω]
    (hpoint : (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).genericExtensionMorphism Ω ≫
      Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) =
      (rationalConfigurationOpen s : Scheme).genericExtensionMorphism Ω) :
    (rationalConfigurationGeometricAmbientMap k κ s Ω).comp
        (algebraMap (RatFunc k) (RatFunc κ)) =
      (algebraMap (rationalConfigurationOpen s : Scheme).functionField Ω).comp
        (rationalConfigurationArithmeticFunctionFieldEquiv k s).toRingHom := by
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
  let _ : SMul (RatFunc k) (RatFunc κ) :=
    (inferInstance : Algebra (RatFunc k) (RatFunc κ)).toSMul
  let : IsScalarTower (RatFunc k) (RatFunc κ) Ω :=
    (rationalConfigurationAmbient_scalarTowers k κ s Ω).2.2.2.1
  apply ambientRingHom_eq_of_functionFieldChartPoint
    (rationalConfigurationOpen s : Scheme)
    (rationalConfigurationArithmeticFunctionFieldEquiv k s)
  change Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫
      rationalConfigurationArithmeticGenericPoint k s = _
  rw [Scheme.functionFieldChartPoint_extend]
  rw [← rationalConfigurationGenericPoint_hpoint k κ s]
  have hchart := rationalConfigurationGenericPoint_hchartpoint k κ s (Ω := Ω)
  dsimp only at hchart
  rw [Category.comp_id] at hchart
  exact (congrArg (· ≫ Limits.pullback.snd
    (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
    ((rationalConfigurationOpen s).ι ≫ π k 1)) hchart.symm).trans hpoint

end AnabelianGeometry.WeightFiltration
