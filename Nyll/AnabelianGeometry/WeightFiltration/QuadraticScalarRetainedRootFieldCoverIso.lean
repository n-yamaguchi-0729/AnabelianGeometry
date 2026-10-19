/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticScalarRefinedBaseCoverIso
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticBoundaryFieldInvariance

/-! # Quadratic Scalar Retained Root Field Cover Iso -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open scoped FintypeCatDiscrete
namespace AnabelianGeometry.WeightFiltration

local instance retainedRootFieldCoverIsoOverCategory (S : Scheme) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme) ⊤ S) :=
  AlgebraicGeometry.FiniteEtale.instCategory S

local instance retainedRootFieldCoverIsoHasPullbacksAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance retainedRootFieldCoverIsoStableUnderBaseChangeAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme)) h hf⟩

theorem quadraticScalar_actual_retainedRootField_coverIso
    (k κ : Type) [Field k] [NumberField k] [Field κ] [Algebra k κ]
    [IsAlgClosure k κ]
    (X : Scheme) (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)
    (W₁ W₂ : FiniteEtale X)
    [Torsor (rootsOfUnity 2 κ)
      ((fiber (xi ≫ Limits.pullback.snd _ f)).obj W₁)]
    [Torsor (rootsOfUnity 2 κ)
      ((fiber (xi ≫ Limits.pullback.snd _ f)).obj W₂)]
    (h₁ : ∀ (p : π₁ᵉᵗ(xi ≫ Limits.pullback.snd _ f))
        (ζ : rootsOfUnity 2 κ) (x : (fiber (xi ≫ Limits.pullback.snd _ f)).obj W₁),
      p • (ζ • x) = restrictRootsOfUnity
        (arithmeticFundamentalGroupHom k κ f (xi ≫ Limits.pullback.snd _ f) p).toRingHom
        2 ζ • (p • x))
    (h₂ : ∀ (p : π₁ᵉᵗ(xi ≫ Limits.pullback.snd _ f))
        (ζ : rootsOfUnity 2 κ) (y : (fiber (xi ≫ Limits.pullback.snd _ f)).obj W₂),
      p • (ζ • y) = restrictRootsOfUnity
        (arithmeticFundamentalGroupHom k κ f (xi ≫ Limits.pullback.snd _ f) p).toRingHom
        2 ζ • (p • y))
    (e : (fiber (xi ≫ Limits.pullback.snd _ f)).obj W₁ ≃
      (fiber (xi ≫ Limits.pullback.snd _ f)).obj W₂)
    (heμ : ∀ (ζ : rootsOfUnity 2 κ) x, e (ζ • x) = ζ • e x)
    (x₀ : (fiber (xi ≫ Limits.pullback.snd _ f)).obj W₁)
    (a : kˣ) (β : κˣ)
    (hβ : β ^ 2 = Units.map (algebraMap k κ).toMonoidHom a)
    (hdisp : ∀ p : π₁ᵉᵗ(xi ≫ Limits.pullback.snd _ f),
      _root_.KummerTheory.rootQuotient (K := k) β
          (arithmeticFundamentalGroupHom k κ f (xi ≫ Limits.pullback.snd _ f) p) =
        ((p • e (p⁻¹ • x₀)) /ₛ e x₀ : rootsOfUnity 2 κ).val)
    {ι : Type} [Finite ι] (ρ : ι → κ) (v : ι → k)
    (hρ : ∀ i, ρ i ^ 2 = algebraMap k κ (v i)) :
    let E := quadraticBoundaryCoordinateField k κ β ρ
    let b := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k E))) f
    let xiE := scalarFiniteBasePoint k κ E X f xi
    let xiX := xi ≫ Limits.pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f
    let hp := scalarFiniteBasePoint_comp_snd k κ E X f xi
    FiniteDimensional k E ∧ NumberField E ∧ IsGalois k E ∧
    (∀ i, (quadraticBoundaryRoot k κ β ρ i : κ) = ρ i) ∧
    (∀ i, quadraticBoundaryRoot k κ β ρ i ^ 2 = algebraMap k E (v i)) ∧
    ∃ j : (FiniteEtale.pullback b).obj W₁ ≅ (FiniteEtale.pullback b).obj W₂,
      ∀ x : (fiber xiE).obj ((FiniteEtale.pullback b).obj W₁),
        pointedPullbackFiberEquiv b xiE xiX hp W₂ ((fiber xiE).map j.hom x) =
          e (pointedPullbackFiberEquiv b xiE xiX hp W₁ x) := by
  intro E b xiE xiX hp
  have hFD : FiniteDimensional k E :=
    quadraticBoundaryCoordinateField_finiteDimensional k κ β ρ
  have hNF : NumberField E := quadraticBoundaryCoordinateField_numberField k κ β ρ
  have hGal : IsGalois k E :=
    quadraticBoundaryCoordinateField_isGalois k κ β ρ a hβ v hρ
  refine ⟨hFD, hNF, hGal, ?_, ?_, ?_⟩
  · intro i
    exact quadraticBoundaryRoot_coe k κ β ρ i
  · intro i
    exact quadraticBoundaryRoot_sq k κ β ρ v hρ i
  · exact quadraticScalar_actual_refinedBase_coverIso k κ X f xi W₁ W₂
      h₁ h₂ e heμ x₀ a β hβ E
      (quadraticScalarField_le_quadraticBoundaryCoordinateField k κ β ρ) hdisp

end AnabelianGeometry.WeightFiltration
