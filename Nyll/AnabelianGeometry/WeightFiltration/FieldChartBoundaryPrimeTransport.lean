/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.GenericPlaceInertiaRingEquiv
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.EtaleFundamentalGroups.Inertia.PlaceNormalizationInertiaRestriction

/-! # The original normalization prime in a reparametrized field chart

The prime in the new valuation ring is obtained from the original Q by the
normalization ring equivalence. The generic point and Ω are unchanged.
This exports the same construction used internally by the field-chart
centralizer theorem, so a final caller can retain its original prime family.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] placeBaseAmbientAlgebra placeBaseAmbientTower

/-- A field-coordinate equivalence transports the specified normalization prime,
with a proved equality of original inertia at the same generic point. -/
theorem exists_fieldChart_normalizationPrime_same_inertia
    {κ F Ω : Type} [Field κ] [Field F] [Algebra κ F]
    (X : Scheme) [IsIntegral X]
    [Algebra κ X.functionField] [Algebra F X.functionField]
    [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    (e : F ≃ₐ[κ] X.functionField)
    (he : ∀ a : F, e a = algebraMap F X.functionField a)
    (p : Place κ F)
    (Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω)) [hQ : Q.IsMaximal] :
    ∃ Q' : Ideal (normalizationCommAlgCat
        (Place.congrRingEquiv e.toRingEquiv e.commutes p).toValuationSubring Ω),
      Q'.IsMaximal ∧ genericPlaceInertia X p Q =
        genericPlaceInertia X (Place.congrRingEquiv e.toRingEquiv e.commutes p) Q' := by
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
  let eN := normalizationIntegralBaseRingEquiv
    p.toValuationSubring p'.toValuationSubring Ω
  let Q' : Ideal (normalizationCommAlgCat p'.toValuationSubring Ω) :=
    Q.comap eN.toRingHom
  have hQ' : Q'.IsMaximal := by
    change (Q.comap eN.toRingHom).IsMaximal
    exact Ideal.comap_isMaximal_of_surjective eN.toRingHom eN.surjective (K := Q) (H := hQ)
  exact ⟨Q', hQ',
    genericPlaceInertia_eq_of_valuationRingEquiv X p p' eV rfl Q⟩

end AnabelianGeometry.WeightFiltration
