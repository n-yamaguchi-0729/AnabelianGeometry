/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.ChosenCuspCommonArithmeticPrime
import Nyll.AnabelianGeometry.WeightFiltration.ArithmeticCorrectionRationalCuspInertia
import Nyll.EtaleFundamentalGroups.GeometricFiber.CommonArithmeticPointGeometricEquiv
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationPrimeInertiaConjugacy

/-!
# Comparing chosen cusp inertia through a common arithmetic point
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve SchemeTheory
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups.Inertia
open scoped RatFunc

namespace AnabelianGeometry.WeightFiltration
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower
  normalizationCommAlgGaloisAction

private theorem chosenAmbient_map_cancel
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

theorem rationalConfigurationChosenInertia_commonPoint_conjugate
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (RatFunc k) Ω] [IsSepClosure (RatFunc k) Ω]
    [Algebra k Ω] [IsScalarTower k (RatFunc k) Ω]
    (A₀ A₁ : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω)
    (H₀ : let : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω := A₀
      IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω)
    (H₁ : let : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω := A₁
      IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω) :
    let U := rationalConfigurationGeometricScheme k κ s
    let X : Scheme := (rationalConfigurationOpen s : Scheme)
    let f := (rationalConfigurationOpen s).ι ≫ π k 1
    let u : U ⟶ X := Limits.pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f
    let x₀ : Spec (.of Ω) ⟶ U := by
      let : Algebra U.functionField Ω := A₀
      exact U.genericExtensionMorphism Ω
    let x₁ : Spec (.of Ω) ⟶ U := by
      let : Algebra U.functionField Ω := A₁
      exact U.genericExtensionMorphism Ω
    let z := Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫
      rationalConfigurationArithmeticGenericPoint k s
    ∀ (h₀ : x₀ ≫ u = z) (h₁ : x₁ ≫ u = z),
    let e := commonArithmeticPointGeometricEquiv k κ X f x₀ x₁ z h₀ h₁
    ∀ p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ s),
    let I₀ : Subgroup (Aut (fiber x₀)) := by
      let : Algebra U.functionField Ω := A₀
      let : IsAlgClosure U.functionField Ω := H₀
      exact rationalConfigurationChosenInertia k κ s Ω p
    let I₁ : Subgroup (Aut (fiber x₁)) := by
      let : Algebra U.functionField Ω := A₁
      let : IsAlgClosure U.functionField Ω := H₁
      exact rationalConfigurationChosenInertia k κ s Ω p
    ∃ g : Aut (fiber x₁),
      I₀.map e.toMonoidHom = I₁.map (MulAut.conj g).toMonoidHom := by
  intro U X f u x₀ x₁ z h₀ h₁ e p I₀ I₁
  let i₀ := (pointedFundamentalGroupHom u x₀ z h₀).toMonoidHom
  let i₁ := (pointedFundamentalGroupHom u x₁ z h₁).toMonoidHom
  let q := (arithmeticFundamentalGroupHom k κ f z).toMonoidHom
  let a := (fieldSourceAbsoluteGaloisHom (RatFunc k) Ω
    (rationalConfigurationArithmeticGenericPoint k s)).toMonoidHom
  obtain ⟨V, hV, hord⟩ :=
    rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p
  have hdata₀ : ∃ Q : Ideal (normalizationCommAlgCat V.toValuationSubring Ω),
      Q.IsMaximal ∧ I₀.map i₀ = (Q.inertia Gal(Ω/RatFunc k)).map a := by
    let : Algebra U.functionField Ω := A₀
    let : IsAlgClosure U.functionField Ω := H₀
    obtain ⟨Q, hQ, hI, _⟩ :=
      rationalConfigurationChosenInertia_commonArithmeticPrime k κ s Ω p V hV hord h₀
    exact ⟨Q, hQ, hI⟩
  have hdata₁ : ∃ Q : Ideal (normalizationCommAlgCat V.toValuationSubring Ω),
      Q.IsMaximal ∧ I₁.map i₁ = (Q.inertia Gal(Ω/RatFunc k)).map a ∧
      ∃ D : Subgroup (Aut (fiber z)),
        D ≤ Subgroup.normalizer (I₁.map i₁ : Set _) ∧
        Function.Surjective (fun d : D => q d.val) := by
    let : Algebra U.functionField Ω := A₁
    let : IsAlgClosure U.functionField Ω := H₁
    exact rationalConfigurationChosenInertia_commonArithmeticPrime k κ s Ω p V hV hord h₁
  obtain ⟨Q₀, hQ₀, hI₀⟩ := hdata₀
  obtain ⟨Q₁, hQ₁, hI₁, D, hDN, hfull⟩ := hdata₁
  have : (show Ideal (integralClosure V.toValuationSubring Ω) from Q₀).IsMaximal := hQ₀
  have : (show Ideal (integralClosure V.toValuationSubring Ω) from Q₁).IsMaximal := hQ₁
  obtain ⟨σ, _, hσ⟩ := normalizationInertiaImages_conjugate_of_maximal V
    (show Ideal (integralClosure V.toValuationSubring Ω) from Q₁)
    (show Ideal (integralClosure V.toValuationSubring Ω) from Q₀) a
  have hconj : I₀.map i₀ = (I₁.map i₁).map (MulAut.conj (a σ)).toMonoidHom := by
    rw [hI₀, hI₁]
    exact hσ
  have hex := commonArithmeticPoint_projection_exact k κ X f x₁ z h₁
  obtain ⟨g, _, _, _, hg⟩ := arithmeticCorrection_exists_geometric_inertia_conjugator
    i₁ q hex.2 I₁ D hDN hfull (a σ)
  refine ⟨g, chosenAmbient_map_cancel i₁ hex.1 (I₀.map e.toMonoidHom)
    (I₁.map (MulAut.conj g).toMonoidHom) ?_⟩
  have hehom : i₁.comp e.toMonoidHom = i₀ := by
    apply MonoidHom.ext
    intro t
    exact commonArithmeticPointGeometricEquiv_projection k κ X f x₀ x₁ z h₀ h₁ t
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
