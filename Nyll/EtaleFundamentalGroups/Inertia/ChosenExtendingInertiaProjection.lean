/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Inertia.ActualExtendingPlaceInertia
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationPrimeInertiaConjugacy

/-! # Actual projection containment for every prescribed upstairs prime

The input R is the caller's prescribed prime on the actual cover function
field. The original connected cover and w construct the localized prime;
actual normalization-prime conjugacy then compares that prime with R.
Thus the caller may retain the prime transported from the fixed rational-model
family. No inertia-containment or root-label preservation is assumed.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
namespace EtaleFundamentalGroups.Inertia
open AlgebraicCurve IsDedekindDomain
open scoped Pointwise
open AnabelianGeometry.WeightFiltration
attribute [local instance]
  Place.instIsFractionRingIntegralClosureAt
  Place.instIsDedekindDomainIntegralClosureAt
  Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  placeBaseAmbientAlgebra placeBaseAmbientTower
  extendingPlaceAmbientAlgebra extendingPlaceAmbientTower
  finiteNormalizationPlaceAlgebra finiteNormalizationPlaceTower
  finiteNormalizationPlaceLocalization finiteNormalizationPlaceAmbientTower
  originalPlaceNormalizationAction extendingPlaceNormalizationAction

/-- Pure group calculation, so rewriting never unfolds the actual cover's
scheme-dependent fundamental-group instances. -/
private theorem conjugate_projection_of_conjugate_eq
    {G H : Type*} [Group G] [Group H]
    (i : G →* H) (a y : G) (b z : H)
    (h : (MulAut.conj b).toMonoidHom z = i y) :
    (MulAut.conj (i a * b)).toMonoidHom z =
      i ((MulAut.conj a).toMonoidHom y) := by
  change b * z * b⁻¹ = i y at h
  change (i a * b) * z * (i a * b)⁻¹ = i (a * y * a⁻¹)
  have hmap : i (a * y * a⁻¹) = i a * i y * (i a)⁻¹ :=
    (i.map_mul (a * y) a⁻¹).trans
      (congrArg₂ (· * ·) (i.map_mul a y) (i.map_inv a))
  calc
    (i a * b) * z * (i a * b)⁻¹ =
        i a * (b * z * b⁻¹) * (i a)⁻¹ := by
      simp only [mul_inv_rev, mul_assoc]
    _ = i a * i y * (i a)⁻¹ :=
      congrArg (fun v => i a * v * (i a)⁻¹) h
    _ = i (a * y * a⁻¹) := hmap.symm

theorem connectedCover_chosenExtendingPlaceInertia_projection
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U]
    (Ω : Type) [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    {k : Type} [Field k] [Algebra k U.functionField]
    (v : Place k U.functionField)
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [Q.IsMaximal]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
    letI : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let K := U.functionField
    let L := W.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra W
    letI : FiniteDimensional K L :=
      finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : Algebra.IsSeparable K L :=
      isSeparable_functionField_of_finiteEtale_isConnected W
    let g := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
    let j := finiteEtaleGenericHomFunctionFieldAlgHom W g
    letI : Algebra L Ω := j.toRingHom.toAlgebra
    letI : IsScalarTower K L Ω := by
      apply IsScalarTower.of_algebraMap_eq'
      ext z
      exact (j.commutes z).symm
    letI : IsSepClosure L Ω :=
      ⟨IsSepClosure.sep_closed K,
        Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
    let jL := W.left.fromSpecStalk (genericPoint W.left)
    let hpoint : (ξ L Ω ≫ jL) ≫ W.hom = U.genericExtensionMorphism Ω :=
      finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W g
    let i := (pointedFundamentalGroupHom W.hom (ξ L Ω ≫ jL)
      (U.genericExtensionMorphism Ω) hpoint).toMonoidHom
    letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
    letI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
    ∀ (r : Place k L), r.restrict K = v →
      ∀ (R : Ideal (integralClosure r.toValuationSubring Ω)), R.IsMaximal →
        ∃ a : π₁ᵉᵗ(U.genericExtensionMorphism Ω),
          (genericPlaceInertia W.left r R).map i ≤
            (genericPlaceInertia U v Q).map (MulAut.conj a).toMonoidHom := by
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let K := U.functionField
  let L := W.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra W
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : Algebra.IsSeparable K L :=
    isSeparable_functionField_of_finiteEtale_isConnected W
  let g := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
  let j := finiteEtaleGenericHomFunctionFieldAlgHom W g
  let : Algebra L Ω := j.toRingHom.toAlgebra
  let : IsScalarTower K L Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    ext z
    exact (j.commutes z).symm
  let : IsSepClosure L Ω :=
    ⟨IsSepClosure.sep_closed K,
      Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
  let jL := W.left.fromSpecStalk (genericPoint W.left)
  let hpoint : (ξ L Ω ≫ jL) ≫ W.hom = U.genericExtensionMorphism Ω :=
    finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W g
  let i := (pointedFundamentalGroupHom W.hom (ξ L Ω ≫ jL)
    (U.genericExtensionMorphism Ω) hpoint).toMonoidHom
  let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  change ∀ (r : Place k L), r.restrict K = v → _
  intro r hr R hR
  let : R.IsMaximal := hR
  obtain ⟨σ₀, P, hP, hPr, hq, himage⟩ :=
    connectedCover_actualExtendingPlaceInertia_image Ω v Q W w r hr
  subst r
  let qB := (σ₀ • Q).comap (normalizationIntegralBaseRingEquiv
    v.toValuationSubring (Place.integralClosureAt L v) Ω).toRingHom
  let qloc := qB.map (normalizationBaseLocalizationRingMap
    (Place.integralClosureAt L v) (Place.placeOfPrime P).toValuationSubring Ω)
  let : qloc.IsMaximal := hq
  let qW := absoluteGenericGaloisToFundamentalGroup W.left Ω
  let qU := absoluteGenericGaloisToFundamentalGroup U Ω
  obtain ⟨σ, _hσ, hconj⟩ := normalizationInertiaImages_conjugate_of_maximal
    (Place.placeOfPrime P) qloc R qW
  have hIR : genericPlaceInertia W.left (Place.placeOfPrime P) R =
      (genericPlaceInertia W.left (Place.placeOfPrime P) qloc).map
        (MulAut.conj (qW σ)).toMonoidHom := by
    rw [genericPlaceInertia_eq_absoluteInertiaImage W.left (Place.placeOfPrime P) R,
      genericPlaceInertia_eq_absoluteInertiaImage W.left (Place.placeOfPrime P) qloc]
    exact hconj
  refine ⟨i (qW σ) * qU σ₀, ?_⟩
  rintro z ⟨x, hx, rfl⟩
  rw [hIR] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyimage : i y ∈ (genericPlaceInertia U v Q).map
      (MulAut.conj (qU σ₀)).toMonoidHom := by
    have hyi : i y ∈ (genericPlaceInertia W.left (Place.placeOfPrime P) qloc).map i :=
      ⟨y, hy, rfl⟩
    rw [himage] at hyi
    exact hyi.1
  obtain ⟨z, hz, hzy⟩ := hyimage
  refine ⟨z, hz, ?_⟩
  exact conjugate_projection_of_conjugate_eq i (qW σ) y (qU σ₀) z hzy

end EtaleFundamentalGroups.Inertia
