/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FunctionField.TamagawaSchemeReconstruction
public import Nyll.EtaleFundamentalGroups.Inertia.GenericSourceCurveModelPlaces
public import Nyll.EtaleFundamentalGroups.Inertia.OpenSourceBoundaryPlaces

/-!
# Realizing the same supplied-field map on the original open models

The actual generic sources make the original proper curves into models of
their supplied fields. Their original stalk places are the model places.
An order-preserving field isomorphism therefore realizes the specified
closed-point correspondence, and boundary preservation restricts that same
model isomorphism to the original opens. The source square retains the
specified field isomorphism, including its semilinear finite scalar map.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.FunctionField

private local instance integralOpenDominant
    {X U : Scheme} [IsIntegral X] [IsIntegral U]
    (j : U ⟶ X) [IsOpenImmersion j] : IsDominant j :=
  ⟨j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j⟩

variable {k F₁ F₂ : Type} [Field k] [Finite k] [Field F₁] [Field F₂]
  [Algebra k F₁] [Algebra k F₂]
  {X₁ X₂ U₁ U₂ : Scheme}
  [IsIntegral X₁] [IsIntegral X₂] [IsIntegral U₁] [IsIntegral U₂]
  (c₁ : X₁ ⟶ Spec (.of k)) [IsProper c₁] [SmoothOfRelativeDimension 1 c₁]
  (j₁ : U₁ ⟶ X₁) [IsOpenImmersion j₁]
  (p₁ : Spec (.of F₁) ⟶ U₁) [IsDominant p₁] [IsPreimmersion p₁]
  (hp₁ : p₁ ≫ (j₁ ≫ c₁) = Spec.map (CommRingCat.ofHom (algebraMap k F₁)))
  (c₂ : X₂ ⟶ Spec (.of k)) [IsProper c₂] [SmoothOfRelativeDimension 1 c₂]
  (j₂ : U₂ ⟶ X₂) [IsOpenImmersion j₂]
  (p₂ : Spec (.of F₂) ⟶ U₂) [IsDominant p₂] [IsPreimmersion p₂]
  (hp₂ : p₂ ≫ (j₂ ≫ c₂) = Spec.map (CommRingCat.ofHom (algebraMap k F₂)))
  (Φ : F₁ ≃+* F₂) (eX : closedPoints X₁ ≃ closedPoints X₂)

local notation "v₁" => genericSourcePlaceEquiv c₁ j₁ p₁ hp₁
local notation "v₂" => genericSourcePlaceEquiv c₂ j₂ p₂ hp₂

/-- The same supplied field isomorphism realizes its original closed
places and open boundary, retaining the literal generic-source square. -/
theorem exists_genericSourceSchemeIso_of_place_order
    (hord : ∀ (x : closedPoints X₁) (a : F₁), (v₂ (eX x)).ord (Φ a) = (v₁ x).ord a)
    (hboundary : ∀ x : closedPoints X₁,
      x.val ∉ Set.range j₁ ↔ (eX x).val ∉ Set.range j₂) :
    ∃ τ : k ≃+* k,
      (∀ a : k, Φ (algebraMap k F₁ a) = algebraMap k F₂ (τ a)) ∧
      ∃ (eC : X₁ ≅ X₂) (u : U₁ ≅ U₂),
        (eC.hom ≫ c₂ ≫ Spec.map (CommRingCat.ofHom τ.toRingHom) = c₁) ∧
        (∀ x : closedPoints X₁, eC.hom x.val = (eX x).val) ∧
        (u.hom ≫ j₂ = j₁ ≫ eC.hom) ∧
        p₁ ≫ u.hom = Spec.map (CommRingCat.ofHom Φ.symm.toRingHom) ≫ p₂ := by
  let hbase₁ : (p₁ ≫ j₁) ≫ c₁ =
      Spec.map (CommRingCat.ofHom (algebraMap k F₁)) := (Category.assoc p₁ j₁ c₁).trans hp₁
  let hbase₂ : (p₂ ≫ j₂) ≫ c₂ =
      Spec.map (CommRingCat.ofHom (algebraMap k F₂)) := (Category.assoc p₂ j₂ c₂).trans hp₂
  let M₁ := CurveModel.ofGenericFieldSource c₁ (p₁ ≫ j₁) hbase₁
  let M₂ := CurveModel.ofGenericFieldSource c₂ (p₂ ≫ j₂) hbase₂
  have : IsOpenImmersion (show U₁ ⟶ M₁.C from j₁) :=
    inferInstanceAs (IsOpenImmersion j₁)
  have : IsOpenImmersion (show U₂ ⟶ M₂.C from j₂) :=
    inferInstanceAs (IsOpenImmersion j₂)
  let v : Place k F₁ ≃ Place k F₂ := (v₁).symm.trans (eX.trans v₂)
  have hplaces₁ : M₁.placeEquiv = v₁ :=
    genericSourceCurveModel_placeEquiv c₁ (p₁ ≫ j₁) hbase₁
  have hplaces₂ : M₂.placeEquiv = v₂ :=
    genericSourceCurveModel_placeEquiv c₂ (p₂ ≫ j₂) hbase₂
  have hv (x : closedPoints X₁) : v (v₁ x) = v₂ (eX x) := by
    change v₂ (eX ((v₁).symm (v₁ x))) = _
    rw [(v₁).symm_apply_apply]
  have horders (P : Place k F₁) (a : F₁) : (v P).ord (Φ a) = P.ord a := by
    obtain ⟨x, rfl⟩ := (v₁).surjective P
    rw [hv]
    exact hord x a
  have hbound (P : Place k F₁) : P ∈ M₁.openBoundaryPlaces j₁ ↔
      v P ∈ M₂.openBoundaryPlaces j₂ := by
    obtain ⟨x, rfl⟩ := (v₁).surjective P
    change (M₁.placeEquiv.symm (v₁ x)).val ∉ Set.range j₁ ↔
      (M₂.placeEquiv.symm (v (v₁ x))).val ∉ Set.range j₂
    rw [hplaces₁, hplaces₂, hv]
    have hleft : ((v₁).symm (v₁ x)).val = x.val :=
      congrArg (fun y : closedPoints X₁ => y.val) ((v₁).symm_apply_apply x)
    have hright : ((v₂).symm (v₂ (eX x))).val = (eX x).val :=
      congrArg (fun y : closedPoints X₂ => y.val) ((v₂).symm_apply_apply (eX x))
    exact (Iff.of_eq (congrArg (fun y : X₁ => y ∉ Set.range j₁) hleft)).trans
      ((hboundary x).trans
        (Iff.of_eq (congrArg (fun y : X₂ => y ∉ Set.range j₂) hright)).symm)
  obtain ⟨Ψ, hΨ, τ, hτ, eC, heC, hfield, hpoint, u, hu⟩ :=
    exists_openSchemeIso_of_multiplicativeExtension_over_finite_constants
      (K₁ := k) (K₂ := k) (U₁ := U₁) (U₂ := U₂) rfl Φ.toMulEquiv v horders
      (RingHom.id F₁) (RingHom.id F₂) Φ (fun _ => rfl) M₁ M₂ j₁ j₂ hbound
  have hΨΦ : Ψ = Φ := by
    apply RingEquiv.ext
    intro a
    exact congrArg (fun f : F₁ ≃* F₂ => f a) hΨ
  subst Ψ
  have hclosed (x : closedPoints X₁) : eC.hom x.val = (eX x).val := by
    have hinput : M₁.placeOfPoint x = v₁ x :=
      (M₁.placeEquiv_apply x).symm.trans
        (congrArg (fun e : closedPoints X₁ ≃ Place k F₁ => e x) hplaces₁)
    have hnorm : M₂.placeEquiv.symm (v (M₁.placeOfPoint x)) = eX x :=
      (congrArg (fun e : closedPoints X₂ ≃ Place k F₂ =>
        e.symm (v (M₁.placeOfPoint x))) hplaces₂).trans
        ((congrArg (v₂).symm (congrArg v hinput)).trans
          ((congrArg (v₂).symm (hv x)).trans ((v₂).symm_apply_apply (eX x))))
    exact (hpoint x).trans (congrArg (fun y : closedPoints X₂ => y.val) hnorm)
  have hcompact := CurveModel.genericSource_comp_iso_eq_of_functionFieldMap Φ M₁ M₂ eC hfield
  rw [CurveModel.ofGenericFieldSource_generic, CurveModel.ofGenericFieldSource_generic]
    at hcompact
  have hsource : p₁ ≫ u.hom = Spec.map (CommRingCat.ofHom Φ.symm.toRingHom) ≫ p₂ := by
    apply (cancel_mono j₂).mp
    have hleft : (p₁ ≫ u.hom) ≫ j₂ = (p₁ ≫ j₁) ≫ eC.hom :=
      (Category.assoc p₁ u.hom j₂).trans
        ((congrArg (fun q : U₁ ⟶ X₂ => p₁ ≫ q) hu).trans
          (Category.assoc p₁ j₁ eC.hom).symm)
    exact hleft.trans (hcompact.trans
      (Category.assoc (Spec.map (CommRingCat.ofHom Φ.symm.toRingHom)) p₂ j₂).symm)
  exact ⟨τ, hτ, eC, u, heC, hclosed, hu, hsource⟩

end AnabelianGeometry.FunctionField
