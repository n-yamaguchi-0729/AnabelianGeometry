/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.OriginalRationalCuspDecompositionImage
import Nyll.AnabelianGeometry.WeightFiltration.ArithmeticCorrectionRationalCuspInertia
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationPrimeInertiaConjugacy
import Nyll.EtaleFundamentalGroups.Inertia.RationalGeometricCuspNormalizer

/-! # Conjugacy of rational cusp inertia in two ambient fields -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve SchemeTheory
open AlgebraicGeometry.FiniteEtale EtaleFundamentalGroups.Inertia
open scoped RatFunc
attribute [local instance] Polynomial.algebra normalizationCommAlgGaloisAction

namespace AnabelianGeometry.WeightFiltration

private theorem twoAmbient_map_cancel
    {G P : Type*} [Group G] [Group P] (i : G →* P)
    (hi : Function.Injective i) (H K : Subgroup G) (h : H.map i = K.map i) : H = K := by
  apply le_antisymm
  · intro x hx
    have hm : i x ∈ K.map i := h ▸ (show i x ∈ H.map i from ⟨x, hx, rfl⟩)
    obtain ⟨y, hy, hyx⟩ := hm
    exact hi hyx ▸ hy
  · intro x hx
    have hm : i x ∈ H.map i := h.symm ▸ (show i x ∈ K.map i from ⟨x, hx, rfl⟩)
    obtain ⟨y, hy, hyx⟩ := hm
    exact hi hyx ▸ hy

local instance twoAmbientIntegralClosureAction
    {A F Ω : Type*} [CommRing A] [Field F] [Field Ω]
    [Algebra A F] [IsFractionRing A F]
    [Algebra F Ω] [Algebra A Ω] [IsScalarTower A F Ω]
    [Algebra.IsAlgebraic F Ω] :
    MulSemiringAction Gal(Ω/F) (integralClosure A Ω) :=
  IsIntegralClosure.MulSemiringAction A F Ω _

private theorem twoAmbient_normalization_inertia_eq
    {A F Ω : Type*} [CommRing A] [Field F] [Field Ω]
    [Algebra A F] [IsFractionRing A F]
    [Algebra F Ω] [Algebra A Ω] [IsScalarTower A F Ω]
    [Algebra.IsAlgebraic F Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) :
    Q.inertia Gal(Ω/F) =
      (show Ideal (integralClosure A Ω) from Q).inertia Gal(Ω/F) := by
  rfl

variable (k κ₀ κ₁ Ω : Type) [Field k] [Field κ₀] [Field κ₁] [Field Ω]
  [Algebra k κ₀] [Algebra k κ₁]
  [Algebra (RatFunc k) Ω]
  [A₀ : Algebra (RatFunc κ₀) Ω] [A₁ : Algebra (RatFunc κ₁) Ω]
  [T₀ : @IsScalarTower (RatFunc k) (RatFunc κ₀) Ω
    (inferInstance : Algebra (RatFunc k) (RatFunc κ₀)).toSMul
    inferInstance inferInstance]
  [T₁ : @IsScalarTower (RatFunc k) (RatFunc κ₁) Ω
    (inferInstance : Algebra (RatFunc k) (RatFunc κ₁)).toSMul
    inferInstance inferInstance]
  [IsAlgClosed κ₀] [IsAlgClosure k κ₀] [IsSepClosure k κ₀]
  [IsAlgClosed κ₁] [IsAlgClosure k κ₁] [IsSepClosure k κ₁]
  [Algebra k Ω] [C₀ : Algebra κ₀ Ω] [C₁ : Algebra κ₁ Ω]
  [K₀ : IsScalarTower k κ₀ Ω] [K₁ : IsScalarTower k κ₁ Ω]
  [IsScalarTower k (RatFunc k) Ω]
  [L₀ : IsScalarTower κ₀ (RatFunc κ₀) Ω] [L₁ : IsScalarTower κ₁ (RatFunc κ₁) Ω]
  [IsGalois (RatFunc k) Ω]
  [IsSepClosure (RatFunc k) Ω] [S₀ : IsSepClosure (RatFunc κ₀) Ω]
  [S₁ : IsSepClosure (RatFunc κ₁) Ω] [IsSepClosed Ω]

omit [IsSepClosure k κ₀] in
theorem twoAmbient_originalPrime_inertia_conjugate
    (V : Place k (RatFunc k)) (hV : V.IsRational)
    (W₀ : Place κ₀ (RatFunc κ₀)) (W₁ : Place κ₁ (RatFunc κ₁))
    (hord₀ : ∀ x : RatFunc k,
      W₀.ord (algebraMap (RatFunc k) (RatFunc κ₀) x) = V.ord x)
    (hord₁ : ∀ x : RatFunc k,
      W₁.ord (algebraMap (RatFunc k) (RatFunc κ₁) x) = V.ord x)
    [Algebra V.toValuationSubring Ω] [@IsScalarTower V.toValuationSubring (RatFunc k) Ω
      (inferInstance : Algebra V.toValuationSubring (RatFunc k)).toSMul
      inferInstance inferInstance]
    [Algebra W₀.toValuationSubring Ω] [Algebra W₁.toValuationSubring Ω]
    [@IsScalarTower W₀.toValuationSubring (RatFunc κ₀) Ω
      (inferInstance : Algebra W₀.toValuationSubring (RatFunc κ₀)).toSMul
      inferInstance inferInstance]
    [@IsScalarTower W₁.toValuationSubring (RatFunc κ₁) Ω
      (inferInstance : Algebra W₁.toValuationSubring (RatFunc κ₁)).toSMul
      inferInstance inferInstance]
    (Q₀ : Ideal (normalizationCommAlgCat W₀.toValuationSubring Ω)) [hQ₀ : Q₀.IsMaximal]
    (Q₁ : Ideal (normalizationCommAlgCat W₁.toValuationSubring Ω)) [hQ₁ : Q₁.IsMaximal]
    {X Y₀ Y₁ : Scheme} [IsIntegral X] [IsIntegral Y₀] [IsIntegral Y₁]
    [F₀ : Algebra (RatFunc κ₀) Y₀.functionField] [F₁ : Algebra (RatFunc κ₁) Y₁.functionField]
    [B₀ : Algebra Y₀.functionField Ω] [B₁ : Algebra Y₁.functionField Ω]
    [U₀ : IsScalarTower (RatFunc κ₀) Y₀.functionField Ω]
    [U₁ : IsScalarTower (RatFunc κ₁) Y₁.functionField Ω]
    [Z₀ : IsSepClosure Y₀.functionField Ω] [Z₁ : IsSepClosure Y₁.functionField Ω]
    (hsurj₀ : Function.Surjective (algebraMap (RatFunc κ₀) Y₀.functionField))
    (hsurj₁ : Function.Surjective (algebraMap (RatFunc κ₁) Y₁.functionField))
    (f : X ⟶ Spec (.of k)) (u₀ : Y₀ ⟶ X) (u₁ : Y₁ ⟶ X)
    (j₀ : Spec (.of (RatFunc κ₀)) ⟶ Y₀) (j₁ : Spec (.of (RatFunc κ₁)) ⟶ Y₁)
    (j : Spec (.of (RatFunc k)) ⟶ X)
    (hchart₀ : Y₀.genericExtensionMorphism Ω ≫ 𝟙 Y₀ =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ₀) Ω)) ≫ j₀)
    (hchart₁ : Y₁.genericExtensionMorphism Ω ≫ 𝟙 Y₁ =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ₁) Ω)) ≫ j₁)
    (hpoint₀ : (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ₀) Ω)) ≫ j₀) ≫ u₀ =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ j)
    (hpoint₁ : (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ₁) Ω)) ≫ j₁) ≫ u₁ =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ j)
    (hbase : (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ j) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    let x₀ := Y₀.genericExtensionMorphism Ω
    let x₁ := Y₁.genericExtensionMorphism Ω
    let z := Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ j
    let hz₀ : x₀ ≫ u₀ = z := by
      dsimp only [x₀, z]
      rw [← hpoint₀, ← hchart₀, Category.comp_id]
    let hz₁ : x₁ ≫ u₁ = z := by
      dsimp only [x₁, z]
      rw [← hpoint₁, ← hchart₁, Category.comp_id]
    let i₀ := (pointedFundamentalGroupHom u₀ x₀ z hz₀).toMonoidHom
    let i₁ := (pointedFundamentalGroupHom u₁ x₁ z hz₁).toMonoidHom
    let q := (arithmeticFundamentalGroupHom k κ₁ f z).toMonoidHom
    ∀ (e : Aut (fiber x₀) ≃* Aut (fiber x₁)),
      (∀ g, i₁ (e g) = i₀ g) → Function.Injective i₁ → i₁.range = q.ker →
      ∃ g : Aut (fiber x₁),
        (genericPlaceInertia Y₀ W₀ Q₀).map e.toMonoidHom =
          (genericPlaceInertia Y₁ W₁ Q₁).map (MulAut.conj g).toMonoidHom := by
  intro x₀ x₁ z hz₀ hz₁ i₀ i₁ q e he hi hex
  let e₀ := ratFuncRationalPlaceNormalizationEquiv V hV W₀ hord₀ (Ω := Ω)
  let e₁ := ratFuncRationalPlaceNormalizationEquiv V hV W₁ hord₁ (Ω := Ω)
  let R₀ : Ideal (normalizationCommAlgCat V.toValuationSubring Ω) := Q₀.comap e₀.symm.toRingHom
  let R₁ : Ideal (normalizationCommAlgCat V.toValuationSubring Ω) := Q₁.comap e₁.symm.toRingHom
  have hR₀ : R₀.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective e₀.symm.toRingHom e₀.symm.surjective
      (K := Q₀) (H := hQ₀)
  have hR₁ : R₁.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective e₁.symm.toRingHom e₁.symm.surjective
      (K := Q₁) (H := hQ₁)
  let a := (fieldSourceAbsoluteGaloisHom (RatFunc k) Ω j).toMonoidHom
  let I₀ : Subgroup (Aut (fiber x₀)) := genericPlaceInertia Y₀ W₀ Q₀
  let I₁ : Subgroup (Aut (fiber x₁)) := genericPlaceInertia Y₁ W₁ Q₁
  have hI₀ : I₀.map i₀ = (R₀.inertia Gal(Ω/RatFunc k)).map a :=
    original_ratFuncPlace_inertia_arithmetic_image V hV W₀ hord₀ Q₀ (hQboundary := hQ₀)
      hsurj₀ u₀ j₀ j hchart₀ hpoint₀
  have hI₁ : I₁.map i₁ = (R₁.inertia Gal(Ω/RatFunc k)).map a :=
    original_ratFuncPlace_inertia_arithmetic_image V hV W₁ hord₁ Q₁ (hQboundary := hQ₁)
      hsurj₁ u₁ j₁ j hchart₁ hpoint₁
  let : (show Ideal (integralClosure V.toValuationSubring Ω) from R₀).IsMaximal := hR₀
  let : (show Ideal (integralClosure V.toValuationSubring Ω) from R₁).IsMaximal := hR₁
  obtain ⟨σ, _, hσ⟩ := normalizationInertiaImages_conjugate_of_maximal V R₁ R₀ a
  have hconj : I₀.map i₀ = (I₁.map i₁).map (MulAut.conj (a σ)).toMonoidHom := by
    rw [hI₀, hI₁, twoAmbient_normalization_inertia_eq R₀,
      twoAmbient_normalization_inertia_eq R₁]
    exact hσ
  let d := a.comp (normalizationDecompositionInclusion V.toValuationSubring (RatFunc k) Ω R₁)
  have hdata : I₁.map i₁ ≤ d.range ∧
      d.range ≤ Subgroup.normalizer (I₁.map i₁ : Set _) ∧
      ∀ τ : Gal(κ₁/k), ∃ γ : Aut (fiber z), γ ∈ d.range ∧ q γ = τ :=
    original_ratFuncPlace_decomposition_image_data V hV W₁ hord₁ Q₁ (hQboundary := hQ₁) hsurj₁
      f u₁ j₁ j hchart₁ hpoint₁ hbase
  have hfull : Function.Surjective (fun t : d.range => q t.val) := by
    intro τ
    obtain ⟨γ, hγ, hqγ⟩ := hdata.2.2 τ
    exact ⟨⟨γ, hγ⟩, hqγ⟩
  obtain ⟨g, _, _, _, hg⟩ := arithmeticCorrection_exists_geometric_inertia_conjugator
    i₁ q hex I₁ d.range hdata.2.1 hfull (a σ)
  refine ⟨g, twoAmbient_map_cancel i₁ hi (I₀.map e.toMonoidHom)
    (I₁.map (MulAut.conj g).toMonoidHom) ?_⟩
  have hehom : i₁.comp e.toMonoidHom = i₀ := MonoidHom.ext he
  have hconjhom : i₁.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (i₁ g)).toMonoidHom.comp i₁ := by
    apply MonoidHom.ext
    intro t
    change i₁ (g * t * g⁻¹) = i₁ g * i₁ t * (i₁ g)⁻¹
    rw [map_mul, map_mul, map_inv]
  calc
    (I₀.map e.toMonoidHom).map i₁ = I₀.map i₀ := by rw [Subgroup.map_map, hehom]
    _ = (I₁.map i₁).map (MulAut.conj (a σ)).toMonoidHom := hconj
    _ = (I₁.map i₁).map (MulAut.conj (i₁ g)).toMonoidHom := hg
    _ = (I₁.map (MulAut.conj g).toMonoidHom).map i₁ := by
      rw [Subgroup.map_map, Subgroup.map_map, hconjhom]

end AnabelianGeometry.WeightFiltration
