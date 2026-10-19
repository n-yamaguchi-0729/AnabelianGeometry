/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareChosenInertiaEndpoint
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareGeometricBoundaryLabels
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareModelInertiaCaller
import Nyll.AlgebraicCurves.Models.Ramification.BoundaryNormalizationPrimes
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineAmbientFields

/-! # Chosen label inertia in named square models -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups EtaleFundamentalGroups.Inertia SchemeTheory
open CategoryTheory.PreGaloisCategory AnabelianGeometry.KummerTheory
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower
  placeBaseAmbientAlgebra placeBaseAmbientTower normalizationCommAlgGaloisAction
namespace AnabelianGeometry.WeightFiltration

local instance chosenLabelInertiaSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

theorem rationalConfigurationChosenInertia_exists_functionFieldPrime
    (k κ : Type) [Field k] [Field κ] [CharZero κ] [Algebra k κ] [Infinite k]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [IsSepClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s)) :
    let U := rationalConfigurationGeometricScheme k κ s
    let _hchar : CharZero U.functionField := Algebra.charZero_of_charZero (R := κ) (A :=
      U.functionField)
    let _hsep : IsSepClosure U.functionField Ω := inferInstance
    let e := rationalConfigurationGeometricFieldAlgEquiv k κ s
    let v := Place.congrRingEquiv e.toRingEquiv e.commutes p.val
    ∃ Q : Ideal (normalizationCommAlgCat v.toValuationSubring Ω),
      Q.IsMaximal ∧ rationalConfigurationChosenInertia k κ s Ω p = genericPlaceInertia U v Q := by
  intro U hchar hsep e v
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : IsScalarTower (RatFunc κ) U.functionField Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : IsAlgClosure (RatFunc κ) Ω := rationalConfigurationAmbient_isAlgClosure_geometric k κ s Ω
  let : IsSepClosure (RatFunc κ) Ω := inferInstance
  let Q := (projectiveLineRatFuncModel κ).boundaryNormalizationPrimes
    (Ω := Ω) (rationalConfigurationBaseChangeChart k κ s) p
  have : Q.IsMaximal := (projectiveLineRatFuncModel κ).boundaryNormalizationPrimes_isMaximal
    (Ω := Ω) (rationalConfigurationBaseChangeChart k κ s) p
  exact fieldChart_prescribedPrime_forward_same_inertia U e (fun _ => rfl) p.val Q

theorem namedSquare_chosen_label_inertia_projection
    (k E κ : Type) [Field k] [Field E] [Field κ] [CharZero κ]
    [Algebra k κ] [Algebra E κ] [Infinite k] [Infinite E]
    (s : Finset (Projectivization k (k × k)))
    (t : Finset (Projectivization E (E × E)))
    [IsNormalIntegral (rationalConfigurationGeometricScheme k κ s)]
    [IsLocallyNoetherian (rationalConfigurationGeometricScheme k κ s)]
    [ConnectedSpace (rationalConfigurationGeometricScheme k κ s)]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [IsSepClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (W : FiniteEtale (rationalConfigurationGeometricScheme k κ s)) [IsConnected W]
    (w : (fiber ((rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω)).obj W)
    (J : W.left ≅ rationalConfigurationGeometricScheme E κ t)
    (qN : rationalConfigurationGeometricScheme E κ t ⟶ rationalConfigurationGeometricScheme k κ s)
    (hJq : J.hom ≫ qN = W.hom)
    (pκ : (projectiveLineRatFuncModel κ).C ⟶ (projectiveLineRatFuncModel κ).C)
    (eκ : RatFunc κ ≃ₐ[κ] RatFunc κ)
    (hplaces : ∀ y : closedPoints (projectiveLineRatFuncModel κ).C,
      ∃ hy : pκ.base y.val ∈ closedPoints (projectiveLineRatFuncModel κ).C,
        (projectiveLineRatFuncModel κ).placeOfPoint ⟨pκ.base y.val, hy⟩ =
          ((projectiveLineRatFuncModel κ).placeOfPoint y).restrictAlong
            (ratFuncPairSquareHom eκ) (ratFuncPairSquareHom_isIntegral eκ))
    (hboundary : ∀ y : (projectiveLineRatFuncModel κ).C,
      y ∉ Set.range (rationalConfigurationBaseChangeChart E κ t) ↔
        pκ y ∉ Set.range (rationalConfigurationBaseChangeChart k κ s))
    (hsquare :
      let _hWIntegral : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
      let _AKL : Algebra (rationalConfigurationGeometricScheme k κ s).functionField
        W.left.functionField :=
        finiteEtaleFunctionFieldAlgebra W
      ∀ z : RatFunc κ,
        J.hom.functionFieldMap J.hom.homeomorph.surjective.denseRange
          (rationalConfigurationGeometricFunctionFieldEquiv E κ t (ratFuncPairSquareHom eκ z)) =
          algebraMap (rationalConfigurationGeometricScheme k κ s).functionField W.left.functionField
            (rationalConfigurationGeometricFunctionFieldEquiv k κ s z)) :
    let cU := rationalConfigurationGeometricFunctionFieldEquiv k κ s
    let N := rationalConfigurationGeometricScheme E κ t
    let K := (rationalConfigurationGeometricScheme k κ s).functionField
    let _AκK : Algebra κ K := (cU.toRingHom.comp (algebraMap κ (RatFunc κ))).toAlgebra
    let _hcharK : CharZero K := Algebra.charZero_of_charZero (R := κ) (A := K)
    let _hSepK : IsSepClosure K Ω := inferInstance
    let _hWIntegral : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let L := W.left.functionField
    let _AKL : Algebra K L := finiteEtaleFunctionFieldAlgebra W
    let lift := fiberObjEquivHom ((rationalConfigurationGeometricScheme k κ
      s).genericExtensionMorphism Ω) W w
    let emb := finiteEtaleGenericHomFunctionFieldAlgHom W lift
    let eR := J.hom.functionFieldRingEquivOfIsOpenImmersion
    let _ANΩ : Algebra N.functionField Ω := (emb.toRingHom.comp eR.toRingHom).toAlgebra
    ∃ hclosure : IsAlgClosure N.functionField Ω,
    let _modelClosure : IsAlgClosure N.functionField Ω := hclosure
    ∃ hN : N.genericExtensionMorphism Ω ≫ qN =
      (rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω,
    ∀ z : t, ∃ a : rationalConfigurationGeometricGroup k κ s Ω,
      (rationalConfigurationChosenInertia E κ t Ω (rationalConfigurationBoundaryPlace E κ t z)).map
        (pointedFundamentalGroupHom qN (N.genericExtensionMorphism Ω)
          ((rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω)
            hN).toMonoidHom ≤
        (rationalConfigurationChosenInertia k κ s Ω
          (rationalConfigurationBoundaryPlace k κ s
            (namedSquareGeometricOriginalLabelProjection k E κ s t pκ eκ hplaces hboundary z))).map
          (MulAut.conj a).toMonoidHom := by
  intro cU N K AκK hcharK hSepK hWIntegral L AKL lift emb eR ANΩ
  have hp := namedSquareChosenInertiaProjection_of_fieldSquare E κ t cU Ω W w J qN eκ hJq hsquare
  change ∃ hclosure : IsAlgClosure N.functionField Ω, _ at hp
  obtain ⟨hclosure, hp⟩ := hp
  let _modelClosure : IsAlgClosure N.functionField Ω := hclosure
  change ∃ hN : N.genericExtensionMorphism Ω ≫ qN =
    (rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω, _ at hp
  obtain ⟨hN, hprojection⟩ := hp
  refine ⟨hclosure, ?_⟩
  intro suppliedClosure
  refine ⟨hN, ?_⟩
  intro z
  let v := rationalConfigurationBoundaryPlace k κ s
    (namedSquareGeometricOriginalLabelProjection k E κ s t pκ eκ hplaces hboundary z)
  obtain ⟨Q, hQ, hQimage⟩ := rationalConfigurationChosenInertia_exists_functionFieldPrime k κ s Ω v
  have hr := namedSquareGeometricOriginalLabelProjection_restrict
    k E κ s t pκ eκ hplaces hboundary z
  obtain ⟨a, ha⟩ := hprojection (rationalConfigurationBoundaryPlace E κ t z) v.val hr Q hQ
  refine ⟨a, ?_⟩
  rw [hQimage]
  exact ha

end AnabelianGeometry.WeightFiltration
