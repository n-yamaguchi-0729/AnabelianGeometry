/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FunctionField.TamagawaAdditivity
public import Nyll.AnabelianGeometry.FunctionField.TamagawaPencilComparison
public import Nyll.AnabelianGeometry.ProjectiveLine.SchemeOpenRestriction
public import Nyll.AlgebraicCurves.FunctionFields.Constants.ConstantsAreBaseAlgClosedTranscendental
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveSeparatingTranscendental
public import Nyll.AlgebraicCurves.Geometry.IsClosedSingletonNeGenericPoint
public import Nyll.AlgebraicCurves.Models.Ramification.OpenBoundary
public import Nyll.AlgebraicCurves.Models.SemilinearFunctionFieldIso
public import Nyll.SchemeTheory.FunctionFields.FiniteConstantFieldIso

/-!
# From the original multiplicative map to the original curve models

Tamagawa's additivity theorem is applied to the given map, its normalized
orders, and its actual principal units. The resulting field isomorphism
therefore has exactly that multiplicative map. Its scalar isomorphism is
constructed and is unique; it is not required to fix the named constants.

The scheme realization retains the exact function-field map and actual
closed-point correspondence. Boundary preservation restricts this same
isomorphism to the original open immersions.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open AnabelianGeometry.ProjectiveLine

namespace AnabelianGeometry.FunctionField

universe v w t₁ t₂

variable {K₁ K₂ : Type} [Field K₁] [Field K₂]
  {F₁ : Type v} {F₂ : Type w} [Field F₁] [Field F₂]
  [Algebra K₁ F₁] [Algebra K₂ F₂]

/-- Corresponding places at the actual boundary determine corresponding
open subschemes, including the generic points of both original curves. -/
theorem exists_openIso_of_modelIso_place_map
    (M₁ : CurveModel K₁ F₁) (M₂ : CurveModel K₂ F₂)
    (v : Place K₁ F₁ ≃ Place K₂ F₂) (e : M₁.C ≅ M₂.C)
    (hpoint : ∀ x : closedPoints M₁.C,
      e.hom x.val = (M₂.placeEquiv.symm (v (M₁.placeOfPoint x))).val)
    {U₁ U₂ : Scheme} [Nonempty U₁] [Nonempty U₂]
    (j₁ : U₁ ⟶ M₁.C) (j₂ : U₂ ⟶ M₂.C)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (hboundary : ∀ P, P ∈ M₁.openBoundaryPlaces j₁ ↔
      v P ∈ M₂.openBoundaryPlaces j₂) :
    ∃ f : U₁ ≅ U₂, f.hom ≫ j₂ = j₁ ≫ e.hom := by
  classical
  have hη₁ : genericPoint M₁.C ∈ Set.range j₁ :=
    ((genericPoint_spec M₁.C).mem_open_set_iff j₁.isOpenEmbedding.isOpen_range).mpr
      ⟨j₁ (Classical.choice (inferInstance : Nonempty U₁)), Set.mem_univ _,
        Set.mem_range_self _⟩
  have hη₂ : genericPoint M₂.C ∈ Set.range j₂ :=
    ((genericPoint_spec M₂.C).mem_open_set_iff j₂.isOpenEmbedding.isOpen_range).mpr
      ⟨j₂ (Classical.choice (inferInstance : Nonempty U₂)), Set.mem_univ _,
        Set.mem_range_self _⟩
  have hdense : DenseRange e.hom :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).surjective.denseRange
  have hopen : e.hom ⁻¹ᵁ j₂.opensRange = j₁.opensRange := by
    ext x
    change e.hom x ∈ Set.range j₂ ↔ x ∈ Set.range j₁
    by_cases hx : x = genericPoint M₁.C
    · subst x
      rw [e.hom.map_genericPoint_of_denseRange hdense]
      exact iff_of_true hη₂ hη₁
    · have hxclosed : IsClosed ({x} : Set M₁.C) :=
        isClosed_singleton_of_ne_genericPoint M₁.toBase x hx
      let P := M₁.placeOfPoint ⟨x, hxclosed⟩
      have hxP : (M₁.placeEquiv.symm P).val = x := by
        change (M₁.placeEquiv.symm (M₁.placeOfPoint ⟨x, hxclosed⟩)).val = x
        rw [← M₁.placeEquiv_apply, M₁.placeEquiv.symm_apply_apply]
      have hyP : (M₂.placeEquiv.symm (v P)).val = e.hom x :=
        (hpoint ⟨x, hxclosed⟩).symm
      have hb := hboundary P
      change (M₁.placeEquiv.symm P).val ∉ Set.range j₁ ↔
        (M₂.placeEquiv.symm (v P)).val ∉ Set.range j₂ at hb
      rw [hxP, hyP] at hb
      exact (not_iff_not.mp hb).symm
  let f : U₁ ≅ U₂ := j₁.isoOpensRange ≪≫
    restrictSchemeIso e j₁.opensRange j₂.opensRange hopen ≪≫ j₂.isoOpensRange.symm
  refine ⟨f, ?_⟩
  change (j₁.isoOpensRange.hom ≫
    (restrictSchemeIso e j₁.opensRange j₂.opensRange hopen).hom ≫
    j₂.isoOpensRange.inv) ≫ j₂ = j₁ ≫ e.hom
  rw [Category.assoc, Category.assoc, Scheme.Hom.isoOpensRange_inv_comp,
    restrictSchemeIso_hom_ι, ← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]

/-- An additive geometric extension realizes the same original finite-field
multiplication on the original open curves. The literal inclusion square
descends additivity; the finite scalar fields are recovered from their common
cardinality, retaining the resulting semilinear structural-map equation. -/
theorem exists_openSchemeIso_of_multiplicativeExtension_over_finite_constants
    [Finite K₁] [Finite K₂] (hcard : Nat.card K₁ = Nat.card K₂)
    (φ : F₁ ≃* F₂) (v : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P z, (v P).ord (φ z) = P.ord z)
    {L₁ : Type t₁} {L₂ : Type t₂} [Field L₁] [Field L₂]
    (i₁ : F₁ →+* L₁) (i₂ : F₂ →+* L₂) (Ψ : L₁ ≃+* L₂)
    (hΨ : ∀ a, Ψ (i₁ a) = i₂ (φ a))
    (M₁ : CurveModel K₁ F₁) (M₂ : CurveModel K₂ F₂)
    {U₁ U₂ : Scheme} [Nonempty U₁] [Nonempty U₂]
    (j₁ : U₁ ⟶ M₁.C) (j₂ : U₂ ⟶ M₂.C)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (hboundary : ∀ P, P ∈ M₁.openBoundaryPlaces j₁ ↔
      v P ∈ M₂.openBoundaryPlaces j₂) :
    ∃ Φ : F₁ ≃+* F₂, Φ.toMulEquiv = φ ∧
      ∃ σ : K₁ ≃+* K₂,
        (∀ a, Φ (algebraMap K₁ F₁ a) = algebraMap K₂ F₂ (σ a)) ∧
        ∃ e : M₁.C ≅ M₂.C,
          (e.hom ≫ M₂.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) = M₁.toBase) ∧
          (∀ (hdense : DenseRange e.hom) (z : F₂),
            e.hom.functionFieldMap hdense (M₂.ffEquiv z) = M₁.ffEquiv (Φ.symm z)) ∧
          (∀ x : closedPoints M₁.C,
            e.hom x.val = (M₂.placeEquiv.symm (v (M₁.placeOfPoint x))).val) ∧
          ∃ f : U₁ ≅ U₂, f.hom ≫ j₂ = j₁ ≫ e.hom := by
  let Φ : F₁ ≃+* F₂ := FieldTheory.ringEquivOfMultiplicativeExtension φ i₁ i₂ Ψ hΨ
  obtain ⟨σ, hσ, -⟩ := FieldTheory.exists_unique_finiteConstantRingEquiv hcard Φ
  obtain ⟨e, he, hfield⟩ :=
    CurveModel.exists_semilinear_iso_functionFieldMap_eq σ Φ hσ M₁ M₂
  have hpoint :=
    CurveModel.iso_apply_closedPoint_of_functionFieldMap Φ v hord M₁ M₂ e hfield
  obtain ⟨f, hf⟩ := exists_openIso_of_modelIso_place_map M₁ M₂ v e hpoint j₁ j₂ hboundary
  exact ⟨Φ, rfl, σ, hσ, e, he, hfield, hpoint, f, hf⟩

variable [IsCurveOver K₁ F₁] [IsCurveOver K₂ F₂]
  [IsAlgClosed K₁] [IsAlgClosed K₂]
  [Algebra.EssFiniteType K₁ F₁] [Algebra.EssFiniteType K₂ F₂]

/-- The scalar isomorphism is reconstructed from the same field map and
normalized orders, and is uniquely determined by the actual scalar maps. -/
theorem exists_unique_constantRingEquiv_of_preserves_orders
    (φ : F₁ ≃+* F₂) (v : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P z, (v P).ord (φ z) = P.ord z) :
    ∃! σ : K₁ ≃+* K₂,
      ∀ a, φ (algebraMap K₁ F₁ a) = algebraMap K₂ F₂ (σ a) := by
  obtain ⟨t₁, ht₁, hfin₁, -⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K₁) (F := F₁)
  obtain ⟨t₂, ht₂, hfin₂, -⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K₂) (F := F₂)
  have : FiniteDimensional (IntermediateField.adjoin K₁ ({t₁} : Set F₁)) F₁ := hfin₁
  have : FiniteDimensional (IntermediateField.adjoin K₂ ({t₂} : Set F₂)) F₂ := hfin₂
  have hC₁ : ConstantsAreBase K₁ F₁ :=
    constantsAreBase_of_isAlgClosed_of_transcendental t₁ ht₁
  have hC₂ : ConstantsAreBase K₂ F₂ :=
    constantsAreBase_of_isAlgClosed_of_transcendental t₂ ht₂
  let m : K₁ →*₀ K₂ := constantMapOfPreservesOrd φ.toMulEquiv v hord hC₂
  have hm (a : K₁) : algebraMap K₂ F₂ (m a) = φ (algebraMap K₁ F₁ a) :=
    constantMapOfPreservesOrd_spec φ.toMulEquiv v hord hC₂ a
  have hbij : Function.Bijective m :=
    ⟨constantMapOfPreservesOrd_injective φ.toMulEquiv v hord hC₂,
      constantMapOfPreservesOrd_surjective φ.toMulEquiv v hord hC₁ hC₂⟩
  let σ : K₁ ≃+* K₂ :=
    { toEquiv := Equiv.ofBijective m hbij
      map_mul' := m.map_mul
      map_add' := fun a b => by
        apply (algebraMap K₂ F₂).injective
        calc
          algebraMap K₂ F₂ (m (a + b)) =
              φ (algebraMap K₁ F₁ (a + b)) := hm (a + b)
          _ = φ (algebraMap K₁ F₁ a) + φ (algebraMap K₁ F₁ b) := by
            rw [map_add, map_add]
          _ = algebraMap K₂ F₂ (m a) + algebraMap K₂ F₂ (m b) := by
            rw [hm a, hm b]
          _ = algebraMap K₂ F₂ (m a + m b) := (map_add _ _ _).symm }
  refine ⟨σ, fun a => (hm a).symm, fun τ hτ => ?_⟩
  apply RingEquiv.ext
  intro a
  apply (algebraMap K₂ F₂).injective
  exact (hτ a).symm.trans (hm a).symm

/-- Additivity and the original scheme realization of the supplied
multiplicative map. No additive or constant-field comparison is an input. -/
theorem exists_schemeIso_of_preserves_orders_and_three_principal_units
    (φ : F₁ ≃* F₂) (v : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P z, (v P).ord (φ z) = P.ord z)
    (S : Set (Place K₁ F₁)) (hS : 3 ≤ S.encard)
    (hunit : ∀ P ∈ S, ∀ z, P.HasValue z 1 ↔ (v P).HasValue (φ z) 1)
    (M₁ : CurveModel K₁ F₁) (M₂ : CurveModel K₂ F₂) :
    ∃ Φ : F₁ ≃+* F₂, Φ.toMulEquiv = φ ∧
      ∃ σ : K₁ ≃+* K₂,
        (∀ a, Φ (algebraMap K₁ F₁ a) = algebraMap K₂ F₂ (σ a)) ∧
        ∃ e : M₁.C ≅ M₂.C,
          (e.hom ≫ M₂.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) = M₁.toBase) ∧
          (∀ (hdense : DenseRange e.hom) (z : F₂),
            e.hom.functionFieldMap hdense (M₂.ffEquiv z) = M₁.ffEquiv (Φ.symm z)) ∧
          ∀ x : closedPoints M₁.C,
            e.hom x.val = (M₂.placeEquiv.symm (v (M₁.placeOfPoint x))).val := by
  let Φ : F₁ ≃+* F₂ :=
    { φ with map_add' := tamagawa_additivity φ v hord S hS hunit }
  obtain ⟨σ, hσ, -⟩ := exists_unique_constantRingEquiv_of_preserves_orders Φ v hord
  obtain ⟨e, he, hfield⟩ :=
    CurveModel.exists_semilinear_iso_functionFieldMap_eq σ Φ hσ M₁ M₂
  exact ⟨Φ, rfl, σ, hσ, e, he, hfield,
    CurveModel.iso_apply_closedPoint_of_functionFieldMap Φ v hord M₁ M₂ e hfield⟩

/-- The same reconstructed map realizes the actual open curve when its
principal-unit and place data are those of the original boundary. -/
theorem exists_openSchemeIso_of_preserves_orders_and_boundary_principal_units
    (φ : F₁ ≃* F₂) (v : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P z, (v P).ord (φ z) = P.ord z)
    (M₁ : CurveModel K₁ F₁) (M₂ : CurveModel K₂ F₂)
    {U₁ U₂ : Scheme} [Nonempty U₁] [Nonempty U₂]
    (j₁ : U₁ ⟶ M₁.C) (j₂ : U₂ ⟶ M₂.C)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (hboundary : ∀ P, P ∈ M₁.openBoundaryPlaces j₁ ↔
      v P ∈ M₂.openBoundaryPlaces j₂)
    (hthree : 3 ≤ (M₁.openBoundaryPlaces j₁).encard)
    (hunit : ∀ P ∈ M₁.openBoundaryPlaces j₁, ∀ z,
      P.HasValue z 1 ↔ (v P).HasValue (φ z) 1) :
    ∃ Φ : F₁ ≃+* F₂, Φ.toMulEquiv = φ ∧
      ∃ σ : K₁ ≃+* K₂,
        (∀ a, Φ (algebraMap K₁ F₁ a) = algebraMap K₂ F₂ (σ a)) ∧
        ∃ e : M₁.C ≅ M₂.C,
          (e.hom ≫ M₂.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) = M₁.toBase) ∧
          (∀ (hdense : DenseRange e.hom) (z : F₂),
            e.hom.functionFieldMap hdense (M₂.ffEquiv z) = M₁.ffEquiv (Φ.symm z)) ∧
          (∀ x : closedPoints M₁.C,
            e.hom x.val = (M₂.placeEquiv.symm (v (M₁.placeOfPoint x))).val) ∧
          ∃ f : U₁ ≅ U₂, f.hom ≫ j₂ = j₁ ≫ e.hom := by
  obtain ⟨Φ, hΦ, σ, hσ, e, he, hfield, hpoint⟩ :=
    exists_schemeIso_of_preserves_orders_and_three_principal_units
      φ v hord (M₁.openBoundaryPlaces j₁) hthree hunit M₁ M₂
  obtain ⟨f, hf⟩ := exists_openIso_of_modelIso_place_map M₁ M₂ v e hpoint j₁ j₂ hboundary
  exact ⟨Φ, hΦ, σ, hσ, e, he, hfield, hpoint, f, hf⟩

end AnabelianGeometry.FunctionField
