/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BareRationalArithmeticScalarRoots
import Nyll.EtaleFundamentalGroups.GeometricFiber.SourceIsoGalois
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisPoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldMonodromyLift

/-!
# The same arithmetic root coordinate for the original RatFunc Galois action

The actual arithmetic chart equivalence extends each original RatFunc Galois
automorphism to the original open function field without changing its ambient
map. Literal point actions identify the two generic constructions at the bare
point. The existing coordinate is retained, as is the source-induced action
used by the one fixed arithmetic base-point correction. No field-action or
base-point compatibility is an additional input.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace AlgebraicCurve
open scoped RatFunc FintypeCatDiscrete

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationOriginalFieldAlgebra rationalConfigurationOriginalConstantAlgebra

local instance (priority := 2000) rootFieldActionSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

private theorem coordinate_sourceIso_eval
    (X : Scheme) [IsIntegral X] (Ω : Type) [Field Ω] [IsSepClosed Ω]
    [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω]
    (n : ℕ) (W : FiniteEtale X) (b : Ω)
    (x : Spec (.of Ω) ⟶ X) (hp : x = X.genericExtensionMorphism Ω)
    (eCan : (fiber (X.genericExtensionMorphism Ω)).obj W ≃ {z : Ω // z ^ n = b})
    (hCan : ∀ (σ : Gal(Ω/X.functionField)) y,
      (eCan ((show π₁ᵉᵗ(X.genericExtensionMorphism Ω) from
        fundamentalGroupHom (X.fromSpecStalk (genericPoint X))
          (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)))
          (toAut (fib X.functionField Ω) Gal(Ω/X.functionField) σ)) • y)).val =
            σ (eCan y).val)
    (eBare : (fiber x).obj W ≃ {z : Ω // z ^ n = b})
    (hBare : ∀ y, eBare y = eCan (((eqToIso (congrArg fiber hp)).hom.app W) y))
    (σ : Gal(Ω/X.functionField))
    (hsource : (Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op).hom ≫ x = x)
    (y : (fiber x).obj W) :
    (eBare ((show π₁ᵉᵗ(x) from
      fiberSourceIso x (Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op) ≪≫
        eqToIso (congrArg fiber hsource)) • y)).val = σ (eBare y).val := by
  subst x
  change ∀ y, eBare y = eCan y at hBare
  let θ := fieldSourceAbsoluteGaloisHom X.functionField Ω
    (X.fromSpecStalk (genericPoint X))
  have hθ : θ σ =
      fiberSourceIso (X.genericExtensionMorphism Ω)
          (Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op) ≪≫
        eqToIso (congrArg fiber hsource) := by
    apply Aut.ext
    ext Z z
    apply (fiberObjEquivHom (X.genericExtensionMorphism Ω) Z).injective
    apply Over.OverMorphism.ext
    exact (fundamentalGroupHom_point_of_point_action
      (X.fromSpecStalk (genericPoint X))
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)))
      (suppliedGaloisEquivFundamentalGroup X.functionField Ω σ) σ.toRingHom
      (suppliedGaloisEquivFundamentalGroup_point X.functionField Ω σ) Z z).trans
      (fiberSourceIso_aut_point (X.genericExtensionMorphism Ω)
        (Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op) hsource Z z).symm
  rw [← hθ, hBare]
  have hθtoAut : θ σ = fundamentalGroupHom (X.fromSpecStalk (genericPoint X))
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)))
      (toAut (fib X.functionField Ω) Gal(Ω/X.functionField) σ) := by
    change fundamentalGroupHom (X.fromSpecStalk (genericPoint X))
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)))
      (toAutHomeo (fib X.functionField Ω) Gal(Ω/X.functionField) σ) = _
    rw [toAutHomeo_apply]
  rw [hθtoAut, hCan, hBare]

/-- Perform the field-chart action comparison before specializing any field
or scheme to the concrete rational configuration. -/
theorem fieldChart_arithmeticRootCoordinate_fieldSource_eval
    (F Ω : Type) [Field F] [Field Ω] [IsSepClosed Ω]
    (X : Scheme) [IsIntegral X]
    [Algebra F X.functionField] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    (E : F ≃+* X.functionField)
    (hfield : algebraMap F X.functionField = E.toRingHom)
    (n : ℕ) (W : FiniteEtale X) (b : Ω)
    (x : Spec (.of Ω) ⟶ X) (hp : x = X.genericExtensionMorphism Ω)
    (eCan : (fiber (X.genericExtensionMorphism Ω)).obj W ≃ {z : Ω // z ^ n = b})
    (hCan : ∀ (σ : Gal(Ω/X.functionField)) y,
      (eCan ((show π₁ᵉᵗ(X.genericExtensionMorphism Ω) from
        fundamentalGroupHom (X.fromSpecStalk (genericPoint X))
          (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)))
          (toAut (fib X.functionField Ω) Gal(Ω/X.functionField) σ)) • y)).val =
            σ (eCan y).val)
    (eBare : (fiber x).obj W ≃ {z : Ω // z ^ n = b})
    (hBare : ∀ y, eBare y = eCan (((eqToIso (congrArg fiber hp)).hom.app W) y)) :
    ∃ hchart : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫
        X.functionFieldChartPoint E = x,
    ∀ σ : Gal(Ω/F),
      let e := Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op
      ∃ hsource : e.hom ≫ x = x,
        (∀ y : (fiber x).obj W,
          (eBare ((show π₁ᵉᵗ(x) from
            fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hsource)) • y)).val =
            σ (eBare y).val) ∧
        continuousConjAut (eqToIso (congrArg fiber hchart))
            (fieldSourceAbsoluteGaloisHom F Ω (X.functionFieldChartPoint E) σ) =
          fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hsource) := by
  have hsurj : Function.Surjective (algebraMap F X.functionField) := by
    rw [hfield]
    exact E.surjective
  have hchartCan : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫
      X.functionFieldChartPoint E = X.genericExtensionMorphism Ω := by
    have hmap : algebraMap F Ω = (algebraMap X.functionField Ω).comp E.toRingHom := by
      rw [IsScalarTower.algebraMap_eq F X.functionField Ω, hfield]
    rw [hmap]
    exact Scheme.functionFieldChartPoint_extend X E
  let hchart := hchartCan.trans hp.symm
  refine ⟨hchart, ?_⟩
  intro σ e
  let σX : Gal(Ω/X.functionField) :=
    AlgEquiv.extendScalarsHomOfSurjective (A := Ω) hsurj σ
  have hfix : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) := by
    change Spec.map (CommRingCat.ofHom σX.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) = _
    rw [← Spec.map_comp]
    exact congrArg (fun z : X.functionField →+* Ω => Spec.map (CommRingCat.ofHom z))
      σX.toAlgHom.comp_algebraMap
  have hsource : e.hom ≫ x = x := by
    rw [hp]
    change e.hom ≫ (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X)) =
        Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
          X.fromSpecStalk (genericPoint X)
    rw [← Category.assoc, hfix]
  refine ⟨hsource, ?_, ?_⟩
  · intro y
    exact coordinate_sourceIso_eval X Ω n W b x hp eCan hCan eBare hBare σX hsource y
  · apply Aut.ext
    ext Z z
    apply (fiberObjEquivHom x Z).injective
    apply Over.OverMorphism.ext
    have hpoint := fundamentalGroupHom_point_of_point_action
      (X.functionFieldChartPoint E)
      (Spec.map (CommRingCat.ofHom (algebraMap F Ω)))
      (suppliedGaloisEquivFundamentalGroup F Ω σ) σ.toRingHom
      (suppliedGaloisEquivFundamentalGroup_point F Ω σ)
    exact (point_action_of_eqToIso hchart _ σ.toRingHom hpoint Z z).trans
      (fiberSourceIso_aut_point x e hsource Z z).symm

/-- Keep the supplied canonical and bare coordinates. Every original RatFunc
Galois automorphism acts on this same bare coordinate by its literal ambient
map, and its original field-source action is exactly the same source action.
Consequently the statement specializes to every chosen normalization prime
without selecting another coordinate or another arithmetic correction. -/
theorem rationalConfiguration_arithmeticRootCoordinate_fieldSource_eval
    (k κ : Type) [Field k] [CharZero k] [Field κ] [Algebra k κ]
    [IsAlgClosed κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (n : ℕ) (W : FiniteEtale (rationalConfigurationOpen s : Scheme)) (b : Ω) :
    let X : Scheme := (rationalConfigurationOpen s : Scheme)
    letI : Algebra X.functionField Ω := rationalConfigurationOriginalAmbientAlgebra k κ s Ω
    letI : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
    letI : IsSepClosure X.functionField Ω :=
      (rationalConfigurationOriginalField_suppliers k κ s Ω).2.2.2.2.1
    letI : IsAlgClosure (RatFunc k) Ω :=
      rationalConfigurationAmbient_isAlgClosure_arithmetic k κ s Ω
    letI : IsSepClosure (RatFunc k) Ω := inferInstance
    let x := rationalConfigurationArithmeticBasePoint k κ s Ω
    ∀ (hp : x = X.genericExtensionMorphism Ω)
      (eCan : (fiber (X.genericExtensionMorphism Ω)).obj W ≃ {z : Ω // z ^ n = b})
      (_hCan : ∀ (σ : Gal(Ω/X.functionField)) y,
        (eCan ((show π₁ᵉᵗ(X.genericExtensionMorphism Ω) from
          fundamentalGroupHom (X.fromSpecStalk (genericPoint X))
            (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)))
            (toAut (fib X.functionField Ω) Gal(Ω/X.functionField) σ)) • y)).val =
              σ (eCan y).val)
      (eBare : (fiber x).obj W ≃ {z : Ω // z ^ n = b})
      (_hBare : ∀ y, eBare y = eCan (((eqToIso (congrArg fiber hp)).hom.app W) y)),
    ∃ hchart : Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫
        rationalConfigurationArithmeticGenericPoint k s = x,
    ∀ σ : Gal(Ω/RatFunc k),
      let e := Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op
      ∃ hsource : e.hom ≫ x = x,
        (∀ y : (fiber x).obj W,
          (eBare ((show π₁ᵉᵗ(x) from
            fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hsource)) • y)).val =
            σ (eBare y).val) ∧
        continuousConjAut (eqToIso (congrArg fiber hchart))
            (fieldSourceAbsoluteGaloisHom (RatFunc k) Ω
              (rationalConfigurationArithmeticGenericPoint k s) σ) =
          fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hsource) := by
  intro X
  let : Algebra X.functionField Ω := rationalConfigurationOriginalAmbientAlgebra k κ s Ω
  let : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
  let : IsSepClosure X.functionField Ω :=
    (rationalConfigurationOriginalField_suppliers k κ s Ω).2.2.2.2.1
  let : IsAlgClosure (RatFunc k) Ω :=
    rationalConfigurationAmbient_isAlgClosure_arithmetic k κ s Ω
  let : IsSepClosure (RatFunc k) Ω := inferInstance
  intro x hp eCan hCan eBare hBare
  let : IsScalarTower (RatFunc k) X.functionField Ω :=
    (rationalConfigurationOriginalField_suppliers k κ s Ω).1
  exact fieldChart_arithmeticRootCoordinate_fieldSource_eval (RatFunc k) Ω X
    (rationalConfigurationArithmeticFunctionFieldEquiv k s) rfl
    n W b x hp eCan hCan eBare hBare

end AnabelianGeometry.WeightFiltration
