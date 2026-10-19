/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.AlignedRationalModelAmbient
import Nyll.AnabelianGeometry.WeightFiltration.SameModelIsoInertia
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.FiniteRationalModelBaseChange
import Nyll.EtaleFundamentalGroups.GeometricFiber.ConstantFieldInclusionFiberPoint
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineAmbientFields
import Nyll.AlgebraicCurves.Models.Charts.OpenChartGenericPoints

/-! # Return the actual rational model point to the original geometric curve

The scalar extension of the specified finite model is the comparison map.
Transporting its generic ambient backwards retains both the original arithmetic
point and the fixed coefficient embedding. These are the point equalities
needed to use the same-place inertia comparison for the original Galois action.
-/

noncomputable section
open AlgebraicGeometry.SmoothProperCurve
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open AnabelianGeometry.GeometricFundamentalGroup
open scoped RatFunc

namespace AnabelianGeometry.WeightFiltration

/-- The actual finite model, with its native arithmetic point, returns a
geometric generic point above exactly the original arithmetic point and the
same coefficient embedding. Both comparisons are obtained from the pullback
projections of the specified model isomorphism. -/
theorem scalarExtensionModelIso_original_genericPoint
    (k E κ Ω : Type) [Field k] [Field E] [Infinite E] [Field κ] [Field Ω]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosed κ] [IsSepClosed Ω]
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
    {X : Scheme} (f : X ⟶ Spec (.of k))
    [IsIntegral (pullback (specMap k κ) f)]
    (s : Finset (Projectivization E (E × E)))
    (J : pullback (specMap k E) f ≅ (rationalConfigurationOpen s : Scheme))
    (hJ : J.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
      pullback.fst (specMap k E) f)
    [Algebra (rationalConfigurationGeometricScheme E κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme E κ s).functionField Ω]
    [Algebra κ Ω]
    (xi : Spec (.of Ω) ⟶ X)
    (hpoint : rationalConfigurationArithmeticBasePoint E κ s Ω =
      arithmeticConstantFieldLift k E κ f xi ≫ J.hom)
    (hcoef : (rationalConfigurationGeometricScheme E κ s).genericExtensionMorphism Ω ≫
      pullback.fst (specMap E κ) ((rationalConfigurationOpen s).ι ≫ π E 1) = ξ κ Ω) :
    let T := scalarExtensionModelIso k E κ f
      ((rationalConfigurationOpen s).ι ≫ π E 1) J hJ
    let _AX : Algebra (pullback (specMap k κ) f).functionField Ω :=
      namedBaseTransportAmbientAlgebra T.symm Ω
    IsAlgClosure (pullback (specMap k κ) f).functionField Ω ∧
      (pullback (specMap k κ) f).genericExtensionMorphism Ω ≫ T.hom =
        (rationalConfigurationGeometricScheme E κ s).genericExtensionMorphism Ω ∧
      (pullback (specMap k κ) f).genericExtensionMorphism Ω ≫
          pullback.fst (specMap k κ) f = ξ κ Ω ∧
      (pullback (specMap k κ) f).genericExtensionMorphism Ω ≫
          pullback.snd (specMap k κ) f = xi := by
  intro T AX
  let x := (pullback (specMap k κ) f).genericExtensionMorphism Ω
  let z := (rationalConfigurationGeometricScheme E κ s).genericExtensionMorphism Ω
  have hback : z ≫ T.inv = x := namedBaseTransport_genericPoint T.symm Ω
  have hforward : x ≫ T.hom = z := by
    rw [← hback, Category.assoc, T.inv_hom_id, Category.comp_id]
  have hrestriction : x ≫ constantCoverRestriction k E κ f =
      arithmeticConstantFieldLift k E κ f xi := by
    apply (cancel_mono J.hom).mp
    calc
      (x ≫ constantCoverRestriction k E κ f) ≫ J.hom =
          x ≫ T.hom ≫ pullback.snd (specMap E κ)
            ((rationalConfigurationOpen s).ι ≫ π E 1) := by
        rw [Category.assoc, ← scalarExtensionModelIso_hom_comp_model]
      _ = z ≫ pullback.snd (specMap E κ)
          ((rationalConfigurationOpen s).ι ≫ π E 1) := by
        rw [← Category.assoc, hforward]
      _ = arithmeticConstantFieldLift k E κ f xi ≫ J.hom := hpoint
  refine ⟨namedBaseTransport_isAlgClosure T.symm Ω, hforward, ?_, ?_⟩
  · calc
      x ≫ pullback.fst (specMap k κ) f =
          x ≫ T.hom ≫ pullback.fst (specMap E κ)
            ((rationalConfigurationOpen s).ι ≫ π E 1) := by
        rw [scalarExtensionModelIso_hom_comp_base]
      _ = z ≫ pullback.fst (specMap E κ)
          ((rationalConfigurationOpen s).ι ≫ π E 1) := by
        rw [← Category.assoc, hforward]
      _ = ξ κ Ω := hcoef
  · calc
      x ≫ pullback.snd (specMap k κ) f =
          (x ≫ constantCoverRestriction k E κ f) ≫ pullback.snd (specMap k E) f := by
        simp only [constantCoverRestriction, Category.assoc, pullback.lift_snd]
      _ = arithmeticConstantFieldLift k E κ f xi ≫ pullback.snd (specMap k E) f := by
        exact congrArg (fun z => z ≫ pullback.snd (specMap k E) f) hrestriction
      _ = xi := arithmeticConstantFieldLift_comp k E κ f xi


/-- The actual coefficient-point equality identifies the canonical rational
coordinate's constants with the already fixed aligned coefficient embedding.
The fixed algebra on Ω is retained; no second coefficient algebra is assumed
to be definitionally the same. -/
theorem rationalConfiguration_fixedConstant_scalarTower
    (k κ : Type) [Field k] [Infinite k] [Field κ] [Algebra k κ]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [Algebra κ Ω]
    (hcoef : (rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω ≫
      pullback.fst (specMap k κ) ((rationalConfigurationOpen s).ι ≫ π k 1) = ξ κ Ω) :
    let _AFΩ : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
    IsScalarTower κ (RatFunc κ) Ω := by
  intro AFΩ
  let : IsIntegral (projectiveLineScheme κ) := projectiveSpace_isIntegral κ 1
  let M := projectiveLineRatFuncModel κ
  let Z := rationalConfigurationGeometricScheme k κ s
  let j : Z ⟶ M.C := rationalConfigurationBaseChangeChart k κ s
  let : IsOpenImmersion j :=
    inferInstanceAs (IsOpenImmersion (rationalConfigurationBaseChangeChart k κ s))
  have hgeneric : Z.genericExtensionMorphism Ω =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫
        Z.functionFieldChartPoint
          (M.ffEquiv.trans j.functionFieldRingEquivOfIsOpenImmersion) := by
    exact (Category.comp_id (Z.genericExtensionMorphism Ω)).symm.trans
      (rationalConfigurationGenericPoint_hchartpoint k κ s (Ω := Ω))
  have hcalc : Z.genericExtensionMorphism Ω ≫ pullback.fst (specMap k κ)
      ((rationalConfigurationOpen s).ι ≫ π k 1) =
        Spec.map (CommRingCat.ofHom
          ((algebraMap (RatFunc κ) Ω).comp (algebraMap κ (RatFunc κ)))) := by
    rw [← rationalConfigurationBaseChangeChart_comp_π k κ s, hgeneric]
    change Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫
      Z.functionFieldChartPoint (M.ffEquiv.trans j.functionFieldRingEquivOfIsOpenImmersion) ≫
        j ≫ M.toBase = _
    rw [← Category.assoc
      (Z.functionFieldChartPoint (M.ffEquiv.trans j.functionFieldRingEquivOfIsOpenImmersion))
      j M.toBase, Scheme.functionFieldChartPoint_comp_openImmersion,
      AlgebraicCurve.CurveModel.functionFieldChartPoint_comp_toBase,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply IsScalarTower.of_algebraMap_eq'
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective (hcoef.symm.trans hcalc))

end AnabelianGeometry.WeightFiltration
