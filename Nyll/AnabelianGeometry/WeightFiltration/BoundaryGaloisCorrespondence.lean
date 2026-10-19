/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryGeometricGaloisAction
import Nyll.AnabelianGeometry.WeightFiltration.AlignedBoundaryGeometricGaloisAction

/-! # Equivariance of the actual geometric cusp correspondence

Both source corrections are retained. The target correction is the ratio
α₂ α₁⁻¹, as dictated by the original arithmetic equivariance. The resulting
label equality is proved from actual inertia ranges and their separation;
it is not an additional assumption on the boundary correspondence.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.SmoothProperCurve
open SchemeTheory EtaleFundamentalGroups.Inertia ProCGroups.Abelian NeronModelInfra

namespace AnabelianGeometry.WeightFiltration

variable
    (k K : Type) [Field k] [Field K] [CharZero K] [IsAlgClosed K]
    [Algebra k K] [IsSepClosure k K]
variable
    {C₁ U₁ : Scheme} [CompactSpace U₁] [QuasiSeparatedSpace U₁]
    (c₁ : C₁ ⟶ Spec (.of k)) (i₁ : U₁ ⟶ C₁)

variable
    [IsIntegral (Limits.pullback (specMap k K) (i₁ ≫ c₁))] [CompactSpace ↑(Limits.pullback (specMap
      k K) (i₁ ≫ c₁))]
    {F₁ : Type} [Field F₁] [Algebra K F₁]
    (M₁ : CurveModel K F₁)
    (eC₁ : M₁.C ≅ pullback c₁ (specMap k K))
    (heC₁ : eC₁.hom ≫ pullback.snd c₁ (specMap k K) = M₁.toBase)
    (j₁ : (Limits.pullback (specMap k K) (i₁ ≫ c₁)) ⟶ M₁.C) [IsOpenImmersion j₁] (hj₁ : DenseRange
      j₁)
    (hproj₁ : j₁ ≫ eC₁.hom ≫ pullback.fst c₁ (specMap k K) = pullback.snd (specMap k K) (i₁ ≫ c₁)
      ≫ i₁)
    (hbase₁ : j₁ ≫ M₁.toBase = pullback.fst (specMap k K) (i₁ ≫ c₁))
    [Algebra F₁ (Limits.pullback (specMap k K) (i₁ ≫ c₁)).functionField]
    (hfield₁ : algebraMap F₁ (Limits.pullback (specMap k K) (i₁ ≫ c₁)).functionField =
      (j₁.functionFieldMap hj₁).comp M₁.ffEquiv.toRingHom)
    {Ω₁ : Type} [Field Ω₁] [Algebra (Limits.pullback (specMap k K) (i₁ ≫ c₁)).functionField Ω₁]
      [Algebra F₁ Ω₁]
    [IsScalarTower F₁ (Limits.pullback (specMap k K) (i₁ ≫ c₁)).functionField Ω₁]
    [IsSepClosed Ω₁] [IsSepClosure (Limits.pullback (specMap k K) (i₁ ≫ c₁)).functionField Ω₁]
      [IsSepClosure F₁ Ω₁]
    [∀ p : M₁.openBoundaryPlaces j₁, Algebra p.val.toValuationSubring Ω₁]
    [∀ p : M₁.openBoundaryPlaces j₁, IsScalarTower p.val.toValuationSubring F₁ Ω₁]
    [Algebra K Ω₁]
    [∀ p : M₁.openBoundaryPlaces j₁, IsScalarTower K p.val.toValuationSubring Ω₁]
    (Q₁ : ∀ p : M₁.openBoundaryPlaces j₁,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω₁))
    [∀ p, (Q₁ p).IsMaximal]

variable
    {C₂ U₂ : Scheme} [CompactSpace U₂] [QuasiSeparatedSpace U₂]
    (c₂ : C₂ ⟶ Spec (.of k)) (i₂ : U₂ ⟶ C₂)

variable
    [IsIntegral (Limits.pullback (specMap k K) (i₂ ≫ c₂))] [CompactSpace ↑(Limits.pullback (specMap
      k K) (i₂ ≫ c₂))]
    {F₂ : Type} [Field F₂] [Algebra K F₂]
    (M₂ : CurveModel K F₂)
    (eC₂ : M₂.C ≅ pullback c₂ (specMap k K))
    (heC₂ : eC₂.hom ≫ pullback.snd c₂ (specMap k K) = M₂.toBase)
    (j₂ : (Limits.pullback (specMap k K) (i₂ ≫ c₂)) ⟶ M₂.C) [IsOpenImmersion j₂] (hj₂ : DenseRange
      j₂)
    (hproj₂ : j₂ ≫ eC₂.hom ≫ pullback.fst c₂ (specMap k K) = pullback.snd (specMap k K) (i₂ ≫ c₂)
      ≫ i₂)
    (hbase₂ : j₂ ≫ M₂.toBase = pullback.fst (specMap k K) (i₂ ≫ c₂))
    [Algebra F₂ (Limits.pullback (specMap k K) (i₂ ≫ c₂)).functionField]
    (hfield₂ : algebraMap F₂ (Limits.pullback (specMap k K) (i₂ ≫ c₂)).functionField =
      (j₂.functionFieldMap hj₂).comp M₂.ffEquiv.toRingHom)
    {Ω₂ : Type} [Field Ω₂] [Algebra (Limits.pullback (specMap k K) (i₂ ≫ c₂)).functionField Ω₂]
      [Algebra F₂ Ω₂]
    [IsScalarTower F₂ (Limits.pullback (specMap k K) (i₂ ≫ c₂)).functionField Ω₂]
    [IsSepClosed Ω₂] [IsSepClosure (Limits.pullback (specMap k K) (i₂ ≫ c₂)).functionField Ω₂]
      [IsSepClosure F₂ Ω₂]
    [∀ p : M₂.openBoundaryPlaces j₂, Algebra p.val.toValuationSubring Ω₂]
    [∀ p : M₂.openBoundaryPlaces j₂, IsScalarTower p.val.toValuationSubring F₂ Ω₂]
    [Algebra K Ω₂]
    [∀ p : M₂.openBoundaryPlaces j₂, IsScalarTower K p.val.toValuationSubring Ω₂]
    (Q₂ : ∀ p : M₂.openBoundaryPlaces j₂,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω₂))
    [∀ p, (Q₂ p).IsMaximal]

variable [IsCurveOver K F₂]

include eC₁ heC₁ hproj₁ hbase₁ eC₂ heC₂ hproj₂ hbase₂ in
/-- An arithmetic-equivariant geometric map, corrected by the two actual
source corrections, forces its recovered cusp labels to follow the literal
coefficient base change. The point formulas identify these with geometric
Galois actions on the compactifications. -/
theorem exists_corrected_boundary_correspondence_galois_equivariance
    (hthree₂ : 3 ≤ Nat.card (M₂.openBoundaryPlaces j₂))
    (e : (TopologicalAbelianization (Aut (fiber ((Limits.pullback (specMap k K) (i₁ ≫
      c₁)).genericExtensionMorphism Ω₁)))) ≃* (TopologicalAbelianization (Aut (fiber
      ((Limits.pullback (specMap k K) (i₂ ≫ c₂)).genericExtensionMorphism Ω₂)))))
    (he : ∀ (σ : K ≃ₐ[k] K) (x : (TopologicalAbelianization (Aut (fiber ((Limits.pullback (specMap
      k K) (i₁ ≫ c₁)).genericExtensionMorphism Ω₁))))), e ((geometricAbelianGaloisAction k K U₁
      (i₁ ≫ c₁) ((Limits.pullback (specMap k K) (i₁ ≫ c₁)).genericExtensionMorphism Ω₁)) σ x) =
      (geometricAbelianGaloisAction k K U₂ (i₂ ≫ c₂) ((Limits.pullback (specMap k K) (i₂ ≫
      c₂)).genericExtensionMorphism Ω₂)) σ (e x))
    (τ₀ : M₁.openBoundaryPlaces j₁ ≃ M₂.openBoundaryPlaces j₂)
    (hτ₀ : ∀ p, ((fun p : M₁.openBoundaryPlaces j₁ =>   (boundaryPlaceInertiaHom M₁ j₁ hj₁ hfield₁
      Q₁ p).toMonoidHom.range) p).map e.toMonoidHom = (fun p : M₂.openBoundaryPlaces j₂ =>
      (boundaryPlaceInertiaHom M₂ j₂ hj₂ hfield₂ Q₂ p).toMonoidHom.range) (τ₀ p)) :
    ∃ α₁ α₂ : K ≃ₐ[k] K,
      ∃ τ : M₁.openBoundaryPlaces j₁ ≃ M₂.openBoundaryPlaces j₂,
      (∀ p, ((fun p : M₁.openBoundaryPlaces j₁ =>   (boundaryPlaceInertiaHom M₁ j₁ hj₁ hfield₁ Q₁
        p).toMonoidHom.range) p).map (e.trans ((geometricAbelianGaloisAction k K U₂ (i₂ ≫ c₂)
        ((Limits.pullback (specMap k K) (i₂ ≫ c₂)).genericExtensionMorphism Ω₂)) (α₂ *
        α₁⁻¹))).toMonoidHom = (fun p : M₂.openBoundaryPlaces j₂ =>   (boundaryPlaceInertiaHom M₂
        j₂ hj₂ hfield₂ Q₂ p).toMonoidHom.range) (τ p)) ∧
      ∀ σ : K ≃ₐ[k] K,
      ∃ (θ₁ : M₁.C ≅ M₁.C) (θ₂ : M₂.C ≅ M₂.C)
        (g₁ : SemilinearAut K F₁) (g₂ : SemilinearAut K F₂),
        (θ₁.hom ≫ eC₁.hom ≫ pullback.fst c₁ (specMap k K) =
            eC₁.hom ≫ pullback.fst c₁ (specMap k K) ∧
          θ₁.hom ≫ M₁.toBase = M₁.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ∧
          SemilinearAut.baseAut g₁ = σ.toRingEquiv ∧
          ∀ z w : SchemeHomOver (𝟙 (Spec (.of K))) M₁.toBase,
            w.1 ≫ θ₁.hom = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ z.1 →
              M₁.pointEquivPlace w = g₁ • M₁.pointEquivPlace z) ∧
        (θ₂.hom ≫ eC₂.hom ≫ pullback.fst c₂ (specMap k K) =
            eC₂.hom ≫ pullback.fst c₂ (specMap k K) ∧
          θ₂.hom ≫ M₂.toBase = M₂.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ∧
          SemilinearAut.baseAut g₂ = σ.toRingEquiv ∧
          ∀ z w : SchemeHomOver (𝟙 (Spec (.of K))) M₂.toBase,
            w.1 ≫ θ₂.hom = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ z.1 →
              M₂.pointEquivPlace w = g₂ • M₂.pointEquivPlace z) ∧
        ∃ (hS₁ : ∀ p : Place K F₁,
              p ∈ M₁.openBoundaryPlaces j₁ ↔ g₁ • p ∈ M₁.openBoundaryPlaces j₁)
          (hS₂ : ∀ p : Place K F₂,
              p ∈ M₂.openBoundaryPlaces j₂ ↔ g₂ • p ∈ M₂.openBoundaryPlaces j₂),
          ∀ p : M₁.openBoundaryPlaces j₁,
            τ ⟨g₁ • p.val, (hS₁ p.val).mp p.property⟩ =
              ⟨g₂ • (τ p).val, (hS₂ (τ p).val).mp (τ p).property⟩ := by
  classical
  obtain ⟨α₁, hα₁⟩ := exists_boundary_geometric_range_action
    k K c₁ i₁ M₁ eC₁ heC₁ j₁ hj₁ hproj₁ hbase₁ hfield₁ Q₁
  obtain ⟨α₂, hα₂⟩ := exists_boundary_geometric_range_action
    k K c₂ i₂ M₂ eC₂ heC₂ j₂ hj₂ hproj₂ hbase₂ hfield₂ Q₂
  obtain ⟨_, gβ, _, _, _, _, hSβ, hrβ⟩ := hα₂ (α₁⁻¹ * α₂)
  let eβ : M₂.openBoundaryPlaces j₂ ≃ M₂.openBoundaryPlaces j₂ :=
    { toFun := fun q => ⟨gβ • q.val, (hSβ q.val).mp q.property⟩
      invFun := fun q => ⟨gβ⁻¹ • q.val, (hSβ (gβ⁻¹ • q.val)).mpr
        (by simpa only [smul_inv_smul] using q.property)⟩
      left_inv := by
        intro q
        apply Subtype.ext
        exact inv_smul_smul gβ q.val
      right_inv := by
        intro q
        apply Subtype.ext
        exact smul_inv_smul gβ q.val }
  let τ := τ₀.trans eβ
  have hproduct : α₂ * (α₁⁻¹ * α₂) * α₂⁻¹ = α₂ * α₁⁻¹ := by
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hτ : ∀ p, ((fun p : M₁.openBoundaryPlaces j₁ =>   (boundaryPlaceInertiaHom M₁ j₁ hj₁
    hfield₁ Q₁ p).toMonoidHom.range) p).map (e.trans ((geometricAbelianGaloisAction k K U₂ (i₂ ≫
    c₂) ((Limits.pullback (specMap k K) (i₂ ≫ c₂)).genericExtensionMorphism Ω₂)) (α₂ *
    α₁⁻¹))).toMonoidHom = (fun p : M₂.openBoundaryPlaces j₂ =>   (boundaryPlaceInertiaHom M₂ j₂
    hj₂ hfield₂ Q₂ p).toMonoidHom.range) (τ p) := by
    intro p
    have hβ := hrβ (τ₀ p)
    rw [hproduct] at hβ
    exact (Subgroup.map_map
      (boundaryPlaceInertiaHom M₁ j₁ hj₁ hfield₁ Q₁ p).toMonoidHom.range
      ((geometricAbelianGaloisAction k K U₂ (i₂ ≫ c₂)
        ((Limits.pullback (specMap k K) (i₂ ≫ c₂)).genericExtensionMorphism Ω₂))
          (α₂ * α₁⁻¹)).toMonoidHom e.toMonoidHom).symm.trans
      ((congrArg (fun H : Subgroup (TopologicalAbelianization (Aut (fiber
          ((Limits.pullback (specMap k K) (i₂ ≫ c₂)).genericExtensionMorphism Ω₂)))) =>
        H.map ((geometricAbelianGaloisAction k K U₂ (i₂ ≫ c₂)
          ((Limits.pullback (specMap k K) (i₂ ≫ c₂)).genericExtensionMorphism Ω₂))
            (α₂ * α₁⁻¹)).toMonoidHom) (hτ₀ p)).trans hβ)
  refine ⟨α₁, α₂, τ, hτ, ?_⟩
  intro σ
  obtain ⟨θ₁, g₁, hθ₁proj, hθ₁base, hg₁, hpoint₁, hS₁, hr₁⟩ := hα₁ σ
  obtain ⟨θ₂, g₂, hθ₂proj, hθ₂base, hg₂, hpoint₂, hS₂, hr₂⟩ := hα₂ σ
  refine ⟨θ₁, θ₂, g₁, g₂, ⟨hθ₁proj, hθ₁base, hg₁, hpoint₁⟩,
    ⟨hθ₂proj, hθ₂base, hg₂, hpoint₂⟩, hS₁, hS₂, ?_⟩
  let : Fintype (M₂.openBoundaryPlaces j₂) := (M₂.openBoundaryPlaces_finite j₂).fintype
  intro p
  exact boundaryRange_correspondence_equivariant
    (fun p : M₁.openBoundaryPlaces j₁ =>   (boundaryPlaceInertiaHom M₁ j₁ hj₁ hfield₁ Q₁
      p).toMonoidHom.range) (fun p : M₂.openBoundaryPlaces j₂ =>   (boundaryPlaceInertiaHom M₂ j₂
      hj₂ hfield₂ Q₂ p).toMonoidHom.range) (boundaryPlaceInertiaHom_range_injective M₂ j₂ hj₂
      hfield₂ Q₂ hthree₂)
    (e.trans ((geometricAbelianGaloisAction k K U₂ (i₂ ≫ c₂) ((Limits.pullback (specMap k K) (i₂ ≫
      c₂)).genericExtensionMorphism Ω₂)) (α₂ * α₁⁻¹))) τ hτ
    ((geometricAbelianGaloisAction k K U₁ (i₁ ≫ c₁) ((Limits.pullback (specMap k K) (i₁ ≫
      c₁)).genericExtensionMorphism Ω₁)) (α₁ * σ * α₁⁻¹)) ((geometricAbelianGaloisAction k K U₂
      (i₂ ≫ c₂) ((Limits.pullback (specMap k K) (i₂ ≫ c₂)).genericExtensionMorphism Ω₂)) (α₂ * σ *
      α₂⁻¹))
    (fun q => ⟨g₁ • q.val, (hS₁ q.val).mp q.property⟩)
    (fun q => ⟨g₂ • q.val, (hS₂ q.val).mp q.property⟩) hr₁ hr₂
    (correctedBoundaryEquiv_intertwines (geometricAbelianGaloisAction k K U₁ (i₁ ≫ c₁)
      ((Limits.pullback (specMap k K) (i₁ ≫ c₁)).genericExtensionMorphism Ω₁))
      (geometricAbelianGaloisAction k K U₂ (i₂ ≫ c₂) ((Limits.pullback (specMap k K) (i₂ ≫
      c₂)).genericExtensionMorphism Ω₂)) e he α₁ α₂ σ) p

section Aligned

variable [Algebra k Ω₁] [IsScalarTower k K Ω₁]
    [Algebra k Ω₂] [IsScalarTower k K Ω₂]

include eC₁ heC₁ hproj₁ hbase₁ eC₂ heC₂ hproj₂ hbase₂ in
/-- When the two coefficient comparisons are aligned, the original recovered
boundary correspondence is Galois equivariant. No change of cusp labels or
coefficient automorphism is needed. -/
theorem boundary_correspondence_galois_equivariance_of_alignedComparison
    (hcoef₁ : ((Limits.pullback (specMap k K) (i₁ ≫ c₁)).genericExtensionMorphism Ω₁) ≫
      pullback.fst (specMap k K) (i₁ ≫ c₁) =
      ξ K Ω₁)
    (hactualBase₁ : (((Limits.pullback (specMap k K) (i₁ ≫ c₁)).genericExtensionMorphism Ω₁) ≫
      pullback.snd (specMap k K) (i₁ ≫ c₁)) ≫
      (i₁ ≫ c₁) = ξ k Ω₁)
    (halign₁ : fieldFiberExtensionIso k K Ω₁ ≪≫
      (eqToIso (congrArg fiber hactualBase₁)).symm =
      ((nonempty_fiber_iso
        ((((Limits.pullback (specMap k K) (i₁ ≫ c₁)).genericExtensionMorphism Ω₁) ≫ pullback.snd
          (specMap k K) (i₁ ≫ c₁)) ≫ (i₁ ≫ c₁))
        (ξ k K)).some).symm)
    (hcoef₂ : ((Limits.pullback (specMap k K) (i₂ ≫ c₂)).genericExtensionMorphism Ω₂) ≫
      pullback.fst (specMap k K) (i₂ ≫ c₂) =
      ξ K Ω₂)
    (hactualBase₂ : (((Limits.pullback (specMap k K) (i₂ ≫ c₂)).genericExtensionMorphism Ω₂) ≫
      pullback.snd (specMap k K) (i₂ ≫ c₂)) ≫
      (i₂ ≫ c₂) = ξ k Ω₂)
    (halign₂ : fieldFiberExtensionIso k K Ω₂ ≪≫
      (eqToIso (congrArg fiber hactualBase₂)).symm =
      ((nonempty_fiber_iso
        ((((Limits.pullback (specMap k K) (i₂ ≫ c₂)).genericExtensionMorphism Ω₂) ≫ pullback.snd
          (specMap k K) (i₂ ≫ c₂)) ≫ (i₂ ≫ c₂))
        (ξ k K)).some).symm)
    (hthree₂ : 3 ≤ Nat.card (M₂.openBoundaryPlaces j₂))
    (e : (TopologicalAbelianization (Aut (fiber ((Limits.pullback (specMap k K) (i₁ ≫
      c₁)).genericExtensionMorphism Ω₁)))) ≃* (TopologicalAbelianization (Aut (fiber
      ((Limits.pullback (specMap k K) (i₂ ≫ c₂)).genericExtensionMorphism Ω₂)))))
    (he : ∀ (σ : K ≃ₐ[k] K) (x : (TopologicalAbelianization (Aut (fiber ((Limits.pullback (specMap
      k K) (i₁ ≫ c₁)).genericExtensionMorphism Ω₁))))), e ((geometricAbelianGaloisAction k K U₁
      (i₁ ≫ c₁) ((Limits.pullback (specMap k K) (i₁ ≫ c₁)).genericExtensionMorphism Ω₁)) σ x) =
      (geometricAbelianGaloisAction k K U₂ (i₂ ≫ c₂) ((Limits.pullback (specMap k K) (i₂ ≫
      c₂)).genericExtensionMorphism Ω₂)) σ (e x))
    (τ : M₁.openBoundaryPlaces j₁ ≃ M₂.openBoundaryPlaces j₂)
    (hτ : ∀ p, ((fun p : M₁.openBoundaryPlaces j₁ =>   (boundaryPlaceInertiaHom M₁ j₁ hj₁ hfield₁
      Q₁ p).toMonoidHom.range) p).map e.toMonoidHom = (fun p : M₂.openBoundaryPlaces j₂ =>
      (boundaryPlaceInertiaHom M₂ j₂ hj₂ hfield₂ Q₂ p).toMonoidHom.range) (τ p)) :
    ∀ σ : K ≃ₐ[k] K,
      ∃ (θ₁ : M₁.C ≅ M₁.C) (θ₂ : M₂.C ≅ M₂.C)
        (g₁ : SemilinearAut K F₁) (g₂ : SemilinearAut K F₂),
        (θ₁.hom ≫ eC₁.hom ≫ pullback.fst c₁ (specMap k K) =
            eC₁.hom ≫ pullback.fst c₁ (specMap k K) ∧
          θ₁.hom ≫ M₁.toBase = M₁.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ∧
          SemilinearAut.baseAut g₁ = σ.toRingEquiv ∧
          ∀ z w : SchemeHomOver (𝟙 (Spec (.of K))) M₁.toBase,
            w.1 ≫ θ₁.hom = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ z.1 →
              M₁.pointEquivPlace w = g₁ • M₁.pointEquivPlace z) ∧
        (θ₂.hom ≫ eC₂.hom ≫ pullback.fst c₂ (specMap k K) =
            eC₂.hom ≫ pullback.fst c₂ (specMap k K) ∧
          θ₂.hom ≫ M₂.toBase = M₂.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ∧
          SemilinearAut.baseAut g₂ = σ.toRingEquiv ∧
          ∀ z w : SchemeHomOver (𝟙 (Spec (.of K))) M₂.toBase,
            w.1 ≫ θ₂.hom = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ z.1 →
              M₂.pointEquivPlace w = g₂ • M₂.pointEquivPlace z) ∧
        ∃ (hS₁ : ∀ p : Place K F₁,
              p ∈ M₁.openBoundaryPlaces j₁ ↔ g₁ • p ∈ M₁.openBoundaryPlaces j₁)
          (hS₂ : ∀ p : Place K F₂,
              p ∈ M₂.openBoundaryPlaces j₂ ↔ g₂ • p ∈ M₂.openBoundaryPlaces j₂),
          ∀ p : M₁.openBoundaryPlaces j₁,
            τ ⟨g₁ • p.val, (hS₁ p.val).mp p.property⟩ =
              ⟨g₂ • (τ p).val, (hS₂ (τ p).val).mp (τ p).property⟩ := by
  classical
  intro σ
  obtain ⟨θ₁, g₁, hθ₁proj, hθ₁base, hg₁, hpoint₁, hS₁, hr₁⟩ :=
    boundary_geometric_range_action_of_alignedComparison
      k K c₁ i₁ M₁ eC₁ heC₁ j₁ hj₁ hproj₁ hbase₁ hfield₁ Q₁
      hcoef₁ hactualBase₁ halign₁ σ
  obtain ⟨θ₂, g₂, hθ₂proj, hθ₂base, hg₂, hpoint₂, hS₂, hr₂⟩ :=
    boundary_geometric_range_action_of_alignedComparison
      k K c₂ i₂ M₂ eC₂ heC₂ j₂ hj₂ hproj₂ hbase₂ hfield₂ Q₂
      hcoef₂ hactualBase₂ halign₂ σ
  refine ⟨θ₁, θ₂, g₁, g₂, ⟨hθ₁proj, hθ₁base, hg₁, hpoint₁⟩,
    ⟨hθ₂proj, hθ₂base, hg₂, hpoint₂⟩, hS₁, hS₂, ?_⟩
  let : Fintype (M₂.openBoundaryPlaces j₂) := (M₂.openBoundaryPlaces_finite j₂).fintype
  intro p
  exact boundaryRange_correspondence_equivariant
    (fun p : M₁.openBoundaryPlaces j₁ =>   (boundaryPlaceInertiaHom M₁ j₁ hj₁ hfield₁ Q₁
      p).toMonoidHom.range) (fun p : M₂.openBoundaryPlaces j₂ =>   (boundaryPlaceInertiaHom M₂ j₂
      hj₂ hfield₂ Q₂ p).toMonoidHom.range) (boundaryPlaceInertiaHom_range_injective M₂ j₂ hj₂
      hfield₂ Q₂ hthree₂)
    e τ hτ ((geometricAbelianGaloisAction k K U₁ (i₁ ≫ c₁) ((Limits.pullback (specMap k K) (i₁ ≫
      c₁)).genericExtensionMorphism Ω₁)) σ) ((geometricAbelianGaloisAction k K U₂ (i₂ ≫ c₂)
      ((Limits.pullback (specMap k K) (i₂ ≫ c₂)).genericExtensionMorphism Ω₂)) σ)
    (fun q => ⟨g₁ • q.val, (hS₁ q.val).mp q.property⟩)
    (fun q => ⟨g₂ • q.val, (hS₂ q.val).mp q.property⟩) hr₁ hr₂ (he σ) p

end Aligned

end AnabelianGeometry.WeightFiltration
