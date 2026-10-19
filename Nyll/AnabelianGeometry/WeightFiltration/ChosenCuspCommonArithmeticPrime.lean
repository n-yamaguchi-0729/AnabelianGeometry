/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.RationalConfigurationMatchedAmbientAction
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalConfigurationCuspRecognition
import Nyll.AnabelianGeometry.WeightFiltration.OriginalRationalCuspDecompositionImage
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationBoundaryPlaceOrders

/-! # A common arithmetic prime for chosen rational cusp inertia

The prescribed geometric normalization prime determines its arithmetic comap
and the existing decomposition data over the original ambient field.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve SchemeTheory
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups.Inertia
open scoped RatFunc

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower
  placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower
  normalizationCommAlgGaloisAction

/-- Convert the carrier presentation and elementwise lifting data before
specializing to the geometric fundamental group. -/
private theorem exists_normalizing_surjective_subgroup
    {G A : Type*} [Group G] (I : Subgroup G) {D : Subgroup G}
    (f : G → A) (hn : D ≤ Subgroup.normalizer I.carrier)
    (hf : ∀ a : A, ∃ g : G, g ∈ D ∧ f g = a) :
    ∃ E : Subgroup G, E ≤ Subgroup.normalizer (I : Set G) ∧
      Function.Surjective (fun g : E => f g.val) := by
  refine ⟨D, hn, ?_⟩
  intro a
  obtain ⟨g, hg, hfg⟩ := hf a
  exact ⟨⟨g, hg⟩, hfg⟩

theorem rationalConfigurationChosenInertia_commonArithmeticPrime
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [Algebra (RatFunc k) Ω] [IsSepClosure (RatFunc k) Ω]
    [Algebra k Ω] [IsScalarTower k (RatFunc k) Ω]
    (p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s))
    (V : Place k (RatFunc k)) (hV : V.IsRational)
    (hord : ∀ t : RatFunc k,
      p.val.ord (algebraMap (RatFunc k) (RatFunc κ) t) = V.ord t)
    (hpoint : (rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω ≫
        Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
          ((rationalConfigurationOpen s).ι ≫ π k 1) =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫
        rationalConfigurationArithmeticGenericPoint k s) :
    let x := (rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω
    let z := Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫
      rationalConfigurationArithmeticGenericPoint k s
    let i := (pointedFundamentalGroupHom
      (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1)) x z hpoint).toMonoidHom
    ∃ Q : Ideal (normalizationCommAlgCat V.toValuationSubring Ω),
      Q.IsMaximal ∧
      (rationalConfigurationChosenInertia k κ s Ω p).map i =
        (Q.inertia Gal(Ω/RatFunc k)).map
          (fieldSourceAbsoluteGaloisHom (RatFunc k) Ω
            (rationalConfigurationArithmeticGenericPoint k s)).toMonoidHom ∧
      ∃ D : Subgroup (Aut (fiber z)),
        D ≤ Subgroup.normalizer ((rationalConfigurationChosenInertia k κ s Ω p).map i : Set _) ∧
        Function.Surjective (fun d : D => arithmeticFundamentalGroupHom k κ
          ((rationalConfigurationOpen s).ι ≫ π k 1) z d.val) := by
  intro x z i
  let U := rationalConfigurationGeometricScheme k κ s
  let j := rationalConfigurationBaseChangeChart k κ s
  let u : U ⟶ (rationalConfigurationOpen s : Scheme) :=
    Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)
  let b := algebraMap (RatFunc k) Ω
  let : CharZero U.functionField := Algebra.charZero_of_charZero (R := κ) (A := U.functionField)
  let : IsSepClosure U.functionField Ω := inferInstance
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
  let : IsScalarTower (RatFunc κ) U.functionField Ω :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower κ (RatFunc κ) Ω := IsScalarTower.of_algebraMap_eq' rfl
  have hchart : U.genericExtensionMorphism Ω ≫ 𝟙 U =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫
        rationalConfigurationGeometricGenericPoint k κ s :=
    rationalConfigurationGenericPoint_hchartpoint k κ s
  let _ : SMul (RatFunc k) (RatFunc κ) :=
    (inferInstance : Algebra (RatFunc k) (RatFunc κ)).toSMul
  have hrestriction : (algebraMap (RatFunc κ) Ω).comp
      (algebraMap (RatFunc k) (RatFunc κ)) = b := by
    apply ambientRingHom_eq_of_functionFieldChartPoint
      (rationalConfigurationOpen s : Scheme)
      (rationalConfigurationArithmeticFunctionFieldEquiv k s)
    let : Algebra (RatFunc k) Ω :=
      ((algebraMap (RatFunc κ) Ω).comp (algebraMap (RatFunc k) (RatFunc κ))).toAlgebra
    let : IsScalarTower (RatFunc k) (RatFunc κ) Ω := IsScalarTower.of_algebraMap_eq' rfl
    change Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫
        rationalConfigurationArithmeticGenericPoint k s = _
    rw [← rationalConfigurationGenericPoint_hpoint k κ s]
    rw [← hchart, Category.comp_id]
    exact hpoint
  let : IsScalarTower (RatFunc k) (RatFunc κ) Ω :=
    IsScalarTower.of_algebraMap_eq' hrestriction.symm
  let : IsScalarTower k κ Ω := by
    apply IsScalarTower.of_algebraMap_eq
    intro t
    rw [IsScalarTower.algebraMap_apply k (RatFunc k) Ω,
      IsScalarTower.algebraMap_apply (RatFunc k) (RatFunc κ) Ω,
      IsScalarTower.algebraMap_apply κ (RatFunc κ) Ω]
    apply congrArg (algebraMap (RatFunc κ) Ω)
    rw [← IsScalarTower.algebraMap_apply k (RatFunc k) (RatFunc κ),
      ← IsScalarTower.algebraMap_apply k κ (RatFunc κ)]
  let : IsAlgClosure (RatFunc κ) Ω :=
    rationalConfigurationAmbient_isAlgClosure_geometric k κ s Ω
  let : IsSepClosure (RatFunc κ) Ω := inferInstance
  let : IsGalois (RatFunc k) Ω := inferInstance
  let Qg := (projectiveLineRatFuncModel κ).boundaryNormalizationPrimes
    (Ω := Ω) j p
  have hQg : Qg.IsMaximal :=
    (projectiveLineRatFuncModel κ).boundaryNormalizationPrimes_isMaximal (Ω := Ω) j p
  let e := ratFuncRationalPlaceNormalizationEquiv V hV p.val hord (Ω := Ω)
  let Qa : Ideal (normalizationCommAlgCat V.toValuationSubring Ω) :=
    Qg.comap e.symm.toRingHom
  have hQa : Qa.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective e.symm.toRingHom e.symm.surjective
      (K := Qg) (H := hQg)
  have hsurj : Function.Surjective (algebraMap (RatFunc κ) U.functionField) :=
    (rationalConfigurationGeometricFunctionFieldEquiv k κ s).surjective
  have hpoint' :
      (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫
        rationalConfigurationGeometricGenericPoint k κ s) ≫ u = z := by
    rw [← hchart, Category.comp_id]
    exact hpoint
  refine ⟨Qa, hQa, ?_, ?_⟩
  · exact original_ratFuncPlace_inertia_arithmetic_image V hV p.val hord Qg
      (hQboundary := hQg) hsurj
      u (rationalConfigurationGeometricGenericPoint k κ s)
      (rationalConfigurationArithmeticGenericPoint k s) hchart hpoint'
  · have hdata := original_ratFuncPlace_decomposition_image_data V hV p.val hord Qg
      (hQboundary := hQg) hsurj
      ((rationalConfigurationOpen s).ι ≫ π k 1) u
      (rationalConfigurationGeometricGenericPoint k κ s)
      (rationalConfigurationArithmeticGenericPoint k s) hchart hpoint'
      (rationalConfigurationGenericPoint_hbasearith k s)
    have hdecomposition := exists_normalizing_surjective_subgroup
      ((genericPlaceInertia U p.val Qg).map i)
      (arithmeticFundamentalGroupHom k κ
        ((rationalConfigurationOpen s).ι ≫ π k 1) z)
      hdata.2.1 hdata.2.2
    exact hdecomposition

end AnabelianGeometry.WeightFiltration
