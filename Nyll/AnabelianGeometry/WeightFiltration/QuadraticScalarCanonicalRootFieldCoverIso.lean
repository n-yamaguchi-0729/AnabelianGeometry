/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticScalarCanonicalBaseEquivariance
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticScalarFiniteBaseCoverIso
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticBoundaryFieldInvariance

/-! # Quadratic Scalar Canonical Root Field Cover Iso -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open scoped FintypeCatDiscrete
namespace AnabelianGeometry.WeightFiltration

local instance rootFieldCanonicalOverCategory (S : Scheme) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme) ⊤ S) :=
  AlgebraicGeometry.FiniteEtale.instCategory S
local instance rootFieldCanonicalHasPullbacksAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun _ _ ↦ inferInstance⟩
local instance rootFieldCanonicalStableUnderBaseChangeAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme)) h hf⟩

theorem quadraticScalar_actual_canonicalRootField_coverIso
    (k κ : Type) [Field k] [NumberField k] [Field κ] [Algebra k κ]
    [IsAlgClosure k κ] [IsAlgClosed κ]
    {X : Scheme} [ConnectedSpace X] (f : X ⟶ Spec (.of k))
    [ConnectedSpace (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f : Scheme)]
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    (W₁ W₂ : FiniteEtale X)
    [Torsor (rootsOfUnity 2 κ) ((fiber xi).obj W₁)]
    [Torsor (rootsOfUnity 2 κ) ((fiber xi).obj W₂)]
    (h₁ : ∀ (p : π₁ᵉᵗ(xi)) (ζ : rootsOfUnity 2 κ) (x : (fiber xi).obj W₁),
      p • (ζ • x) = restrictRootsOfUnity
        (arithmeticFundamentalGroupHom k κ f xi p).toRingHom 2 ζ • (p • x))
    (h₂ : ∀ (p : π₁ᵉᵗ(xi)) (ζ : rootsOfUnity 2 κ) (x : (fiber xi).obj W₂),
      p • (ζ • x) = restrictRootsOfUnity
        (arithmeticFundamentalGroupHom k κ f xi p).toRingHom 2 ζ • (p • x))
    (e : (fiber xi).obj W₁ ≃ (fiber xi).obj W₂)
    (heμ : ∀ (ζ : rootsOfUnity 2 κ) x, e (ζ • x) = ζ • e x)
    (x₀ : (fiber xi).obj W₁) (β : κˣ)
    (hdisp : ∀ p : π₁ᵉᵗ(xi),
      _root_.KummerTheory.rootQuotient (K := k) β
        (arithmeticFundamentalGroupHom k κ f xi p) =
          ((p • e (p⁻¹ • x₀)) /ₛ e x₀ : rootsOfUnity 2 κ).val)
    {ι : Type} [Finite ι] (ρ : ι → κ) :
    let E := quadraticBoundaryCoordinateField k κ β ρ
    let _hFD : FiniteDimensional k E :=
      quadraticBoundaryCoordinateField_finiteDimensional k κ β ρ
    let _hsep : Algebra.IsSeparable k E := inferInstance
    let _hFE : IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
      constantField_specMap_isFiniteEtale k E
    let b := ((FiniteEtale.pullback f).obj (originalConstantFieldCover k E)).hom
    let xiE := arithmeticConstantFieldLift k E κ f xi
    let hp := arithmeticConstantFieldLift_comp k E κ f xi
    ∃ j : (FiniteEtale.pullback b).obj W₁ ≅ (FiniteEtale.pullback b).obj W₂,
      ∀ x : (fiber xiE).obj ((FiniteEtale.pullback b).obj W₁),
        pointedPullbackFiberEquiv b xiE xi hp W₂ ((fiber xiE).map j.hom x) =
          e (pointedPullbackFiberEquiv b xiE xi hp W₁ x) := by
  intro E hFD hsep hFE b xiE hp
  have hconn : ConnectedSpace
      (((FiniteEtale.pullback f).obj (originalConstantFieldCover k E)).left) :=
    scalarFiniteBase_connectedSpace k κ E X f
  exact quadraticScalar_actual_canonicalBase_coverIso k κ E f xi
    W₁ W₂ h₁ h₂ e heμ x₀ β
    (scalar_mem_quadraticBoundaryCoordinateField k κ β ρ) hdisp

end AnabelianGeometry.WeightFiltration
