/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalConfigurationCuspRecognition
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaProcyclic
import Nyll.AnabelianGeometry.WeightFiltration.NamedModelCoverGroupSquare
import Nyll.AnabelianGeometry.WeightFiltration.NamedModelPointedInertia
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineBoundaryPlaces
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineAmbientFields
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineFunctionFields
import Nyll.AlgebraicCurves.Models.Ramification.BoundaryNormalizationPrimes
import Nyll.EtaleFundamentalGroups.GeometricFiber.RecoveredCoverGenericPoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps

/-! # Nontrivial named inertia and injective model projections -/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open CategoryTheory.PreGaloisCategory
open SchemeTheory EtaleFundamentalGroups EtaleFundamentalGroups.Inertia
open scoped RatFunc

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower
  placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower

local instance chosenInertiaSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

theorem rationalConfigurationChosenInertia_exists_ne_one
    (k κ : Type) [Field k] [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k κ] [Infinite k]
    (s : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s)) :
    ∃ z : rationalConfigurationGeometricGroup k κ s Ω,
      z ∈ rationalConfigurationChosenInertia k κ s Ω p ∧ z ≠ 1 := by
  let U := rationalConfigurationGeometricScheme k κ s
  let M := projectiveLineRatFuncModel κ
  let j : U ⟶ M.C := rationalConfigurationBaseChangeChart k κ s
  let : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (rationalConfigurationBaseChangeChart k κ s))
  let : CharZero U.functionField :=
    Algebra.charZero_of_charZero (R := κ) (A := U.functionField)
  let : IsSepClosure U.functionField Ω := inferInstance
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
  let : IsScalarTower (RatFunc κ) U.functionField Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower κ (RatFunc κ) Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : IsAlgClosure (RatFunc κ) Ω :=
    rationalConfigurationAmbient_isAlgClosure_geometric k κ s Ω
  let : IsSepClosure (RatFunc κ) Ω := inferInstance
  let : IsCurveOver κ (RatFunc κ) := AlgebraicCurve.instIsCurveOverRatFunc κ
  let : Finite (M.openBoundaryPlaces j) := rationalConfigurationBoundaryPlaces_finite k κ s
  let : Nontrivial (M.openBoundaryPlaces j) :=
    rationalConfigurationBoundaryPlaces_nontrivial k κ s hs
  let Q := M.boundaryNormalizationPrimes (Ω := Ω) j
  let : ∀ q : M.openBoundaryPlaces j, (Q q).IsMaximal := fun q => inferInstance
  have hj : DenseRange j := rationalConfigurationBaseChangeChart_denseRange k κ s
  have hfield : algebraMap (RatFunc κ) U.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom :=
    rationalConfigurationGeometricFunctionFieldEquiv_hfield k κ s
  change ∃ z : rationalConfigurationGeometricGroup k κ s Ω,
    z ∈ genericPlaceInertia U p.val (Q p) ∧ z ≠ 1
  exact boundaryInertia_exists_ne_one M j hj hfield Q p

theorem namedSquare_induced_model_projection_injective
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U]
    (Ω : Type) [Field Ω] [IsSepClosed Ω] [Algebra U.functionField Ω]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W)
    {N : Scheme} [IsIntegral N] (J : W.left ≅ N)
    (qN : N ⟶ U) (hJq : J.hom ≫ qN = W.hom) :
    let _hWIntegral : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let _AKL : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let lift := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
    let emb := finiteEtaleGenericHomFunctionFieldAlgHom W lift
    let _ALΩ : Algebra W.left.functionField Ω := emb.toRingHom.toAlgebra
    let e := J.hom.functionFieldRingEquivOfIsOpenImmersion
    let _ANΩ : Algebra N.functionField Ω := (emb.toRingHom.comp e.toRingHom).toAlgebra
    ∀ hN : N.genericExtensionMorphism Ω ≫ qN = U.genericExtensionMorphism Ω,
      Function.Injective (pointedFundamentalGroupHom qN (N.genericExtensionMorphism Ω)
        (U.genericExtensionMorphism Ω) hN) := by
  intro hWIntegral AKL lift emb ALΩ e ANΩ hN
  have hmodel : N.genericExtensionMorphism Ω =
      actualFiberPointLift (U.genericExtensionMorphism Ω) W w ≫ J.hom := by
    exact recoveredCover_genericExtensionMorphism_eq W w J.symm
      (actualFiberPointLift (U.genericExtensionMorphism Ω) W w ≫ J.hom)
      ((Category.assoc _ J.hom J.inv).trans
        ((congrArg (fun z : W.left ⟶ W.left =>
          actualFiberPointLift (U.genericExtensionMorphism Ω) W w ≫ z)
          J.hom_inv_id).trans (Category.comp_id _)))
  have htransport (y : Spec (.of Ω) ⟶ N)
      (hy : y = actualFiberPointLift (U.genericExtensionMorphism Ω) W w ≫ J.hom)
      (hyq : y ≫ qN = U.genericExtensionMorphism Ω) :
      Function.Injective (pointedFundamentalGroupHom qN y
        (U.genericExtensionMorphism Ω) hyq) := by
    subst y
    exact namedModelProjection_injective W (U.genericExtensionMorphism Ω) w J qN hJq
  exact htransport _ hmodel hN

end AnabelianGeometry.WeightFiltration
