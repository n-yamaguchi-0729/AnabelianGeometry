/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.GenericPlaceInertiaRingEquiv
import Nyll.AnabelianGeometry.WeightFiltration.NamedModelPointedInertia
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.EtaleFundamentalGroups.Inertia.PlaceNormalizationInertiaRestriction

/-! # Keep the localized original prime while changing to the named field chart


The prime in the new valuation ring is obtained from the original Q by the
normalization ring equivalence. The generic point and Ω are unchanged.
This exports the same construction used internally by the field-chart
centralizer theorem, so a final caller can retain its original prime family.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve SchemeTheory EtaleFundamentalGroups.Inertia
open CategoryTheory AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] placeBaseAmbientAlgebra placeBaseAmbientTower
  normalizationCommAlgGaloisAction

/-- The original localized normalization prime R remains unchanged. Its inverse
transport supplies a prime in the rational coordinate chart, with the same
inertia at the actual generic point. This is the direction needed after
connectedCover_actualPlaceInertia_image has already fixed R. -/
theorem exists_fieldChart_originalPrime_same_inertia
    {κ F Ω : Type} [Field κ] [Field F] [Algebra κ F]
    (X : Scheme) [IsIntegral X]
    [Algebra κ X.functionField] [Algebra F X.functionField]
    [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    (e : F ≃ₐ[κ] X.functionField)
    (he : ∀ a : F, e a = algebraMap F X.functionField a)
    (p : Place κ F)
    (R : Ideal (normalizationCommAlgCat
      (Place.congrRingEquiv e.toRingEquiv e.commutes p).toValuationSubring Ω))
    [hR : R.IsMaximal] :
    ∃ Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω),
      Q.IsMaximal ∧ genericPlaceInertia X p Q =
        genericPlaceInertia X (Place.congrRingEquiv e.toRingEquiv e.commutes p) R := by
  let p' := Place.congrRingEquiv e.toRingEquiv e.commutes p
  let eV : p.toValuationSubring ≃+* p'.toValuationSubring :=
    Place.congrValuationSubringEquiv e.toRingEquiv e.commutes p
  let : Algebra p.toValuationSubring p'.toValuationSubring := eV.toRingHom.toAlgebra
  let : IsScalarTower p.toValuationSubring p'.toValuationSubring Ω := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    calc
      algebraMap p.toValuationSubring Ω a = algebraMap F Ω (a : F) :=
        IsScalarTower.algebraMap_apply p.toValuationSubring F Ω a
      _ = algebraMap X.functionField Ω (algebraMap F X.functionField (a : F)) :=
        IsScalarTower.algebraMap_apply F X.functionField Ω (a : F)
      _ = algebraMap X.functionField Ω (e (a : F)) :=
        congrArg (algebraMap X.functionField Ω) (he (a : F)).symm
      _ = algebraMap p'.toValuationSubring Ω (eV a) :=
        (IsScalarTower.algebraMap_apply p'.toValuationSubring X.functionField Ω (eV a)).symm
  let : Algebra.IsIntegral p.toValuationSubring p'.toValuationSubring := by
    refine ⟨fun b => ?_⟩
    obtain ⟨a, rfl⟩ := eV.surjective b
    exact isIntegral_algebraMap
  let eN : normalizationCommAlgCat p'.toValuationSubring Ω ≃+*
      normalizationCommAlgCat p.toValuationSubring Ω :=
    normalizationIntegralBaseRingEquiv
    p.toValuationSubring p'.toValuationSubring Ω
  let Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω) :=
    R.comap eN.symm.toRingHom
  have hQ : Q.IsMaximal := by
    change (R.comap eN.symm.toRingHom).IsMaximal
    exact Ideal.comap_isMaximal_of_surjective
      eN.symm.toRingHom eN.symm.surjective (K := R) (H := hR)
  have hQR : Q.comap eN.toRingHom = R := by
    ext z
    change eN.symm (eN z) ∈ R ↔ z ∈ R
    rw [eN.symm_apply_apply]
  refine ⟨Q, hQ, ?_⟩
  have hI := genericPlaceInertia_eq_of_valuationRingEquiv X p p' eV rfl Q
  change genericPlaceInertia X p Q = genericPlaceInertia X p' (Q.comap eN.toRingHom) at hI
  exact hI.trans (congrArg (fun I : Ideal (normalizationCommAlgCat
    p'.toValuationSubring Ω) => genericPlaceInertia X p' I) hQR)

/-- The actual localized prime R is mapped through the specified named-model
morphism. Its chart prime Q is derived, and the pointed inertia equality is
proved. In application hpoint is namedModel_coordinate_ambient_comp combined
with the same-w generic embedding, never a new coordinate-preservation input. -/
theorem exists_fieldChart_originalPrime_pointed_image
    {κ F Ω : Type} [Field κ] [Field F] [Algebra κ F]
    (X Z : Scheme) [IsIntegral X] [IsIntegral Z]
    [Algebra κ X.functionField] [Algebra F X.functionField]
    [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    (e : F ≃ₐ[κ] X.functionField)
    (he : ∀ a : F, e a = algebraMap F X.functionField a)
    (p : Place κ F)
    (R : Ideal (normalizationCommAlgCat
      (Place.congrRingEquiv e.toRingEquiv e.commutes p).toValuationSubring Ω))
    [R.IsMaximal]
    (f : X ⟶ Z) (jF : Spec (.of F) ⟶ Z)
    (hpoint : X.genericExtensionMorphism Ω ≫ f = ξ F Ω ≫ jF) :
    ∃ Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω),
      Q.IsMaximal ∧
      (genericPlaceInertia X (Place.congrRingEquiv e.toRingEquiv e.commutes p) R).map
        (pointedFundamentalGroupHom f (X.genericExtensionMorphism Ω)
          (ξ F Ω ≫ jF) hpoint).toMonoidHom =
        (Q.inertia Gal(Ω/F)).map (fieldSourceAbsoluteGaloisHom F Ω jF).toMonoidHom := by
  obtain ⟨Q, hQ, hI⟩ := exists_fieldChart_originalPrime_same_inertia X e he p R
  have hsurj : Function.Surjective (algebraMap F X.functionField) := by
    intro z
    obtain ⟨a, ha⟩ := e.surjective z
    exact ⟨a, (he a).symm.trans ha⟩
  refine ⟨Q, hQ, ?_⟩
  rw [← hI]
  exact genericPlaceInertia_pointed_morphism_chart_image X Z f p Q hsurj jF hpoint

end AnabelianGeometry.WeightFiltration
