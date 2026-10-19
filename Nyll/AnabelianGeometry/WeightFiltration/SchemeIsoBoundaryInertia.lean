/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareLiteralBaseTransport
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareModelInertiaCaller

/-!
# Actual inertia under a change of geometric scheme model

The ambient embedding is transported through the function-field map of the
specified scheme isomorphism. The generic-point equality is then a theorem,
not a separate compatibility assumption. A prescribed normalization prime on
the target supplies the source prime by the actual valuation-ring isomorphism.
This applies in particular to a constant-field tower isomorphism; it does not
assert that an arbitrary semilinear permutation of cusps has a linear realization.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open AlgebraicCurve SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] placeBaseAmbientAlgebra placeBaseAmbientTower
  normalizationCommAlgGaloisAction

/-- Transport of the ambient field along an actual scheme isomorphism preserves
being a separable closure, in arbitrary characteristic. -/
theorem namedBaseTransport_isSepClosure
    {U V : Scheme} [IsIntegral U] [IsIntegral V] (e : U ≅ V)
    (Ω : Type) [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] :
    let _A : Algebra V.functionField Ω := namedBaseTransportAmbientAlgebra e Ω
    IsSepClosure V.functionField Ω := by
  intro A
  let eF := e.hom.functionFieldRingEquivOfIsOpenImmersion
  have he : (algebraMap V.functionField Ω).comp eF.symm.toRingHom =
      (RingEquiv.refl Ω).toRingHom.comp (algebraMap U.functionField Ω) := by
    ext a
    change algebraMap U.functionField Ω (eF (eF.symm a)) =
      algebraMap U.functionField Ω a
    rw [eF.apply_symm_apply]
  exact ⟨IsSepClosure.sep_closed U.functionField,
    Algebra.IsSeparable.of_equiv_equiv eF.symm (RingEquiv.refl Ω) he⟩

/-- The actual pointed map of an isomorphism carries the transported prime's
inertia to the prescribed target inertia. Only compatibility of the actual
function-field map with the coefficient field is required. In particular no
point-transport or inertia-transport equality is assumed. -/
theorem schemeIso_prescribedPrime_pointed_inertia
    {k Ω : Type} [Field k] [Field Ω]
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [Algebra k X.functionField] [Algebra k Y.functionField]
    (e : X ≅ Y)
    (he : ∀ a : k,
      e.hom.functionFieldRingEquivOfIsOpenImmersion
        (algebraMap k Y.functionField a) = algebraMap k X.functionField a)
    [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω] [IsSepClosed Ω] :
    let eF : Y.functionField ≃ₐ[k] X.functionField :=
      { e.hom.functionFieldRingEquivOfIsOpenImmersion with commutes' := he }
    let _AYX : Algebra Y.functionField X.functionField := eF.toRingHom.toAlgebra
    let _AYΩ : Algebra Y.functionField Ω := namedBaseTransportAmbientAlgebra e Ω
    let _hYXΩ : IsScalarTower Y.functionField X.functionField Ω :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _hSepY : IsSepClosure Y.functionField Ω := namedBaseTransport_isSepClosure e Ω
    let hpoint := namedBaseTransport_genericPoint e Ω
    ∀ (p : Place k Y.functionField)
      (Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω)),
      Q.IsMaximal →
      ∃ R : Ideal (normalizationCommAlgCat
          (Place.congrRingEquiv eF.toRingEquiv eF.commutes p).toValuationSubring Ω),
        R.IsMaximal ∧
        (genericPlaceInertia X (Place.congrRingEquiv eF.toRingEquiv eF.commutes p) R).map
          (pointedFundamentalGroupHom e.hom (X.genericExtensionMorphism Ω)
            (Y.genericExtensionMorphism Ω) hpoint).toMonoidHom =
          genericPlaceInertia Y p Q := by
  intro eF AYX AYΩ hYXΩ hSepY hpoint p Q hQ
  let : Q.IsMaximal := hQ
  obtain ⟨R, hR, hforward⟩ :=
    fieldChart_prescribedPrime_forward_same_inertia X eF (fun _ => rfl) p Q
  refine ⟨R, hR, ?_⟩
  rw [← hforward]
  have hsurj : Function.Surjective (algebraMap Y.functionField X.functionField) :=
    eF.surjective
  have h := genericPlaceInertia_pointed_morphism_chart_image X Y e.hom p Q
    hsurj (Y.fromSpecStalk (genericPoint Y)) hpoint
  rw [genericPlaceInertia_eq_absoluteInertiaImage Y p Q,
    absoluteGenericGaloisToFundamentalGroup_eq_fieldSourceAbsoluteGaloisHom]
  exact h

/-- Passing to a commutative image removes the choice of a maximal
normalization prime at the same actual place. The coefficient field need not
be algebraically closed. -/
theorem genericPlaceInertia_commutative_image_independent
    {k Ω : Type} [Field k] [Field Ω]
    (X : Scheme) [IsIntegral X] [Algebra k X.functionField]
    [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω] [IsSepClosed Ω]
    (p : Place k X.functionField)
    (Q R : Ideal (normalizationCommAlgCat p.toValuationSubring Ω))
    [Q.IsMaximal] [R.IsMaximal]
    {A : Type*} [CommGroup A] (q : π₁ᵉᵗ(X.genericExtensionMorphism Ω) →* A) :
    (genericPlaceInertia X p Q).map q = (genericPlaceInertia X p R).map q := by
  let qX := absoluteGenericGaloisToFundamentalGroup X Ω
  obtain ⟨σ, _, hconj⟩ :=
    @normalizationInertiaImages_conjugate_of_maximal k X.functionField Ω
      _ _ _ _ _ _ p _ _ Q R
      (inferInstanceAs (Q.IsMaximal)) (inferInstanceAs (R.IsMaximal)) A _ (q.comp qX)
  have hid : (MulAut.conj ((q.comp qX) σ)).toMonoidHom = MonoidHom.id A := by
    apply MonoidHom.ext
    intro a
    change ((q.comp qX) σ) * a * ((q.comp qX) σ)⁻¹ = a
    rw [mul_comm ((q.comp qX) σ) a, mul_assoc, mul_inv_cancel, mul_one]
  rw [hid, Subgroup.map_id] at hconj
  rw [genericPlaceInertia_eq_absoluteInertiaImage X p Q,
    genericPlaceInertia_eq_absoluteInertiaImage X p R, Subgroup.map_map, Subgroup.map_map]
  exact hconj.symm

end AnabelianGeometry.WeightFiltration
