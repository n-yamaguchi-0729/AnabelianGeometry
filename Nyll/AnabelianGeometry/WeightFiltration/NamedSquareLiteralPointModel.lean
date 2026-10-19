/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareMatchedPointModel
import Nyll.AnabelianGeometry.WeightFiltration.RationalConfigurationMatchedGenericAmbient
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareLiteralBaseTransport
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareLiteralGeometricMap
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineGenericPoints
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineBoundaryPlaces
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineGeometry
import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionField
import Nyll.EtaleFundamentalGroups.GeometricFiber.RecoveredCoverGenericPoint

/-!
# Literal generic points for named square models
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve TopologicalSpace
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups CategoryTheory.PreGaloisCategory
open AnabelianGeometry.KummerTheory
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AnabelianGeometry.WeightFiltration

local instance literalPoint_projectiveIntegral (F : Type) [Field F] :
    IsIntegral (projectiveLineScheme F) := projectiveSpace_isIntegral F 1

theorem namedModelAmbientAlgebra_eq_of_genericPoint
    {U N : Scheme} [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    [IsIntegral N]
    {Ω : Type} [Field Ω] [IsSepClosed Ω] [Algebra U.functionField Ω]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) (J : W.left ≅ N)
    (A : Algebra N.functionField Ω)
    (hpoint : let : Algebra N.functionField Ω := A
      N.genericExtensionMorphism Ω =
        actualFiberPointLift (U.genericExtensionMorphism Ω) W w ≫ J.hom) :
    let _hW : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let _AW : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let lift := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
    let emb := finiteEtaleGenericHomFunctionFieldAlgHom W lift
    (emb.toRingHom.comp J.hom.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra = A := by
  intro hW AW lift emb
  let : Algebra N.functionField Ω := A
  let b : N.functionField →+* Ω :=
    emb.toRingHom.comp J.hom.functionFieldRingEquivOfIsOpenImmersion.toRingHom
  have hb := recoveredCover_genericExtensionMorphism_eq W w J.symm
    (actualFiberPointLift (U.genericExtensionMorphism Ω) W w ≫ J.hom)
    (by
      change (actualFiberPointLift (U.genericExtensionMorphism Ω) W w ≫ J.hom) ≫
          J.inv = actualFiberPointLift (U.genericExtensionMorphism Ω) W w
      rw [Category.assoc, J.hom_inv_id, Category.comp_id])
  have hspec : Spec.map (CommRingCat.ofHom b) ≫ N.fromSpecStalk (genericPoint N) =
      Spec.map (CommRingCat.ofHom (algebraMap N.functionField Ω)) ≫
        N.fromSpecStalk (genericPoint N) := hb.trans hpoint.symm
  have hcat : CommRingCat.ofHom b =
      CommRingCat.ofHom (algebraMap N.functionField Ω) := by
    apply Spec.map_injective
    exact (cancel_mono (N.fromSpecStalk (genericPoint N))).mp hspec
  have hring : b = algebraMap N.functionField Ω := congrArg CommRingCat.Hom.hom hcat
  apply Algebra.algebra_ext
  intro z
  exact RingHom.congr_fun hring z

variable (k E κ : Type) [Field k] [Field E] [Field κ] [Infinite k] [Infinite E]
variable [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
variable (s : Finset (Projectivization k (k × k)))
local notation "G" => pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
  (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
    (Scheme.Opens.ι (rationalConfigurationOpen s) ≫ π k 1))
local notation "V" => rationalConfigurationGeometricScheme k κ s

local instance literalPoint_matchedIntegral : IsIntegral G :=
  rationalConfiguration_coefficientTower_isIntegral k E κ s
local instance literalPoint_matchedNormal : IsNormalIntegral G :=
  namedSquareMatchedBase_isNormalIntegral k E κ s
local instance literalPoint_matchedNoetherian : IsLocallyNoetherian G :=
  namedSquareMatchedBase_isLocallyNoetherian k E κ s

omit [Infinite k] [Infinite E] in
theorem namedSquareConstantProjectionChart_range :
    Set.range (namedSquareConstantProjectionChart k E κ s) =
      Set.range (rationalConfigurationBaseChangeChart k κ s) := by
  rw [← namedSquareConstantProjectionIso_chart k E κ s]
  change Set.range (fun x => rationalConfigurationBaseChangeChart k κ s
      ((namedSquareConstantProjectionIso k E κ s).hom x)) = _
  ext z
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(namedSquareConstantProjectionIso k E κ s).hom x, hx⟩
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := (namedSquareConstantProjectionIso k E κ s).hom.homeomorph.surjective x
    exact ⟨y, (congrArg (rationalConfigurationBaseChangeChart k κ s) hy).trans hx⟩

omit [Infinite k] [Infinite E] in
theorem namedSquareConstantProjectionChart_boundary_card :
    Nat.card ((projectiveLineRatFuncModel κ).openBoundaryPlaces
      (namedSquareConstantProjectionChart k E κ s)) = s.card := by
  have hplaces : (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (namedSquareConstantProjectionChart k E κ s) =
      (projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ s) := by
    apply Set.ext
    intro p
    change ((projectiveLineRatFuncModel κ).placeEquiv.symm p).val ∉
        Set.range (namedSquareConstantProjectionChart k E κ s) ↔
      ((projectiveLineRatFuncModel κ).placeEquiv.symm p).val ∉
        Set.range (rationalConfigurationBaseChangeChart k κ s)
    rw [namedSquareConstantProjectionChart_range k E κ s]
  rw [hplaces, rationalConfigurationBoundaryPlaces_card k κ s]

theorem namedSquareLiteralModel_field
    (W : FiniteEtale G) [IsConnected W]
    (t : Finset (Projectivization E (E × E)))
    (J : W.left ≅ rationalConfigurationGeometricScheme E κ t)
    (eκ : RatFunc κ ≃ₐ[κ] RatFunc κ)
    [IsOpenImmersion (namedSquareConstantProjectionChart k E κ s)]
    (hfield :
      let _hW : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
      let _AW : Algebra (G).functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
      ∀ z : RatFunc κ,
        J.hom.functionFieldMap J.hom.homeomorph.surjective.denseRange
          (rationalConfigurationGeometricFunctionFieldEquiv E κ t (ratFuncPairSquareHom eκ z)) =
        algebraMap (G).functionField W.left.functionField
          (((projectiveLineRatFuncModel κ).ffEquiv.trans
            (namedSquareConstantProjectionChart k E κ s).functionFieldRingEquivOfIsOpenImmersion)
              z)) :
    let WL := namedCoverOnIsomorphicBase (namedSquareConstantProjectionIso k E κ s) W
    let _hWL : IsConnected WL := namedCoverOnIsomorphicBase_isConnected _ W
    let _hW : IsIntegral WL.left := isIntegral_left_of_isConnected_finiteEtale WL
    let _AW : Algebra (V).functionField WL.left.functionField := finiteEtaleFunctionFieldAlgebra WL
    ∀ z : RatFunc κ,
      (show WL.left ⟶ rationalConfigurationGeometricScheme E κ t from J.hom).functionFieldMap
        J.hom.homeomorph.surjective.denseRange
        (rationalConfigurationGeometricFunctionFieldEquiv E κ t (ratFuncPairSquareHom eκ z)) =
      algebraMap (V).functionField WL.left.functionField
        (rationalConfigurationGeometricFunctionFieldEquiv k κ s z) := by
  intro WL hWL hW AW z
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  have hjG : DenseRange (namedSquareConstantProjectionChart k E κ s) :=
    (namedSquareConstantProjectionChart k E κ
      s).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _
  have hjV : DenseRange (rationalConfigurationBaseChangeChart k κ s) :=
    (rationalConfigurationBaseChangeChart k κ
      s).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _
  have h := namedCoverOnIsomorphicBase_chart_field_square
    (namedSquareConstantProjectionIso k E κ s) W
    (finiteEtale_hom_denseRange_of_isConnected W)
    (namedSquareConstantProjectionChart k E κ s)
    (rationalConfigurationBaseChangeChart k κ s) hjG hjV
    (namedSquareConstantProjectionIso_chart k E κ s)
    ((projectiveLineRatFuncModel κ).ffEquiv z)
  exact (hfield z).trans h.symm

theorem namedSquare_matchedModel_exists_literal_model
    (Ω : Type) [Field Ω] [IsSepClosed Ω]
    [Algebra (G).functionField Ω] [IsAlgClosure (G).functionField Ω]
    (W : FiniteEtale G) [IsConnected W]
    (w : (fiber ((G).genericExtensionMorphism Ω)).obj W)
    (t : Finset (Projectivization E (E × E)))
    (J : W.left ≅ rationalConfigurationGeometricScheme E κ t)
    (eκ : RatFunc κ ≃ₐ[κ] RatFunc κ)
    (p : (projectiveLineRatFuncModel κ).C ⟶ (projectiveLineRatFuncModel κ).C)
    [IsOpenImmersion (namedSquareConstantProjectionChart k E κ s)]
    (hboundary : ∀ z : (projectiveLineRatFuncModel κ).C,
      z ∉ Set.range (rationalConfigurationBaseChangeChart E κ t) ↔
        p z ∉ Set.range (namedSquareConstantProjectionChart k E κ s))
    (hfield :
      let _hW : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
      let _AW : Algebra (G).functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
      ∀ z : RatFunc κ,
        J.hom.functionFieldMap J.hom.homeomorph.surjective.denseRange
          (rationalConfigurationGeometricFunctionFieldEquiv E κ t (ratFuncPairSquareHom eκ z)) =
        algebraMap (G).functionField W.left.functionField
          (((projectiveLineRatFuncModel κ).ffEquiv.trans
            (namedSquareConstantProjectionChart k E κ s).functionFieldRingEquivOfIsOpenImmersion)
              z))
    [Algebra (rationalConfigurationGeometricScheme E κ t).functionField Ω]
    (hmodel : (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω =
      actualFiberPointLift ((G).genericExtensionMorphism Ω) W w ≫ J.hom) :
    let iso := namedSquareConstantProjectionIso k E κ s
    let _A : Algebra (V).functionField Ω := namedBaseTransportAmbientAlgebra iso Ω
    let WL := namedCoverOnIsomorphicBase iso W
    let _hWL : IsConnected WL := namedCoverOnIsomorphicBase_isConnected iso W
    IsAlgClosure (V).functionField Ω ∧
    ∃ wL : (fiber ((V).genericExtensionMorphism Ω)).obj WL,
      actualFiberPointLift ((V).genericExtensionMorphism Ω) WL wL =
        actualFiberPointLift ((G).genericExtensionMorphism Ω) W w ∧
      J.hom ≫ (J.inv ≫ WL.hom) = WL.hom ∧
      (∀ z : (projectiveLineRatFuncModel κ).C,
        z ∉ Set.range (rationalConfigurationBaseChangeChart E κ t) ↔
          p z ∉ Set.range (rationalConfigurationBaseChangeChart k κ s)) ∧
      (let _hW : IsIntegral WL.left := isIntegral_left_of_isConnected_finiteEtale WL
       let _AW : Algebra (V).functionField WL.left.functionField :=
         finiteEtaleFunctionFieldAlgebra WL
       ∀ z : RatFunc κ,
         (show WL.left ⟶ rationalConfigurationGeometricScheme E κ t from J.hom).functionFieldMap
           J.hom.homeomorph.surjective.denseRange
           (rationalConfigurationGeometricFunctionFieldEquiv E κ t (ratFuncPairSquareHom eκ z)) =
         algebraMap (V).functionField WL.left.functionField
           (rationalConfigurationGeometricFunctionFieldEquiv k κ s z)) ∧
      (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω =
        actualFiberPointLift ((V).genericExtensionMorphism Ω) WL wL ≫ J.hom ∧
      (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω ≫
          (J.inv ≫ WL.hom) = (V).genericExtensionMorphism Ω := by
  intro iso A WL hWL
  refine ⟨namedBaseTransport_isAlgClosure iso Ω, ?_⟩
  have hpoint := namedBaseTransport_genericPoint iso Ω
  have hw : ∃ wL : (fiber ((V).genericExtensionMorphism Ω)).obj WL,
      actualFiberPointLift ((V).genericExtensionMorphism Ω) WL wL =
        actualFiberPointLift ((G).genericExtensionMorphism Ω) W w := by
    rw [← hpoint]
    exact ⟨namedCoverOnIsomorphicBasePoint iso W ((G).genericExtensionMorphism Ω) w,
      namedCoverOnIsomorphicBasePoint_lift iso W ((G).genericExtensionMorphism Ω) w⟩
  obtain ⟨wL, hwL⟩ := hw
  have hm : (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω =
      actualFiberPointLift ((V).genericExtensionMorphism Ω) WL wL ≫ J.hom := by
    rw [hwL]
    exact hmodel
  refine ⟨wL, hwL, J.hom_inv_id_assoc WL.hom, ?_,
    namedSquareLiteralModel_field k E κ s W t J eκ hfield, hm, ?_⟩
  · intro z
    simpa only [namedSquareConstantProjectionChart_range k E κ s] using hboundary z
  · exact (congrArg (fun a => a ≫ (J.inv ≫ WL.hom)) hm).trans
      ((Category.assoc (actualFiberPointLift ((V).genericExtensionMorphism Ω) WL wL)
        J.hom (J.inv ≫ WL.hom)).trans
        ((congrArg (fun a => actualFiberPointLift ((V).genericExtensionMorphism Ω) WL wL ≫ a)
          (J.hom_inv_id_assoc WL.hom)).trans
          (actualFiberPointLift_comp ((V).genericExtensionMorphism Ω) WL wL)))

end AnabelianGeometry.WeightFiltration
