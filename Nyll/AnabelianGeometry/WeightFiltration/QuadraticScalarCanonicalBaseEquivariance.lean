/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticScalarFiniteBaseEquivariance
import Nyll.EtaleFundamentalGroups.GeometricFiber.ConstantFieldInclusionFiberPoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.EquivariantFiberCoverIso

/-! # The same radical and fibre map at the canonical finite-base point

The original arithmetic comparison selects the actual finite-base point. Its
image fixes the specified intermediate field pointwise, hence fixes the same
radical β already occurring in the original displacement. The unchanged e and
x₀ therefore give an actual isomorphism of the same pulled-back named covers.
No new scalar, root, fibre map, or equality of characters is assumed.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open scoped FintypeCatDiscrete

namespace AnabelianGeometry.WeightFiltration

local instance canonicalQuadraticCoverIsoOverCategory (S : Scheme) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme) ⊤ S) :=
  AlgebraicGeometry.FiniteEtale.instCategory S

local instance canonicalQuadraticCoverIsoHasPullbacksAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance canonicalQuadraticCoverIsoStableUnderBaseChangeAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme)) h hf⟩

/-- The semilinear torsor calculation is reused from
`QuadraticScalarFiniteBaseEquivariance`, with the original displacement point. -/
private theorem canonical_equivariant_of_semilinear_displacement_eq_one
    {P A X Y : Type*} [Group P] [Group A]
    [Torsor A X] [Torsor A Y] [MulAction P X] [MulAction P Y]
    (p : P) (φ : A → A)
    (hX : ∀ (a : A) (x : X), p • (a • x) = φ a • (p • x))
    (hY : ∀ (a : A) (y : Y), p • (a • y) = φ a • (p • y))
    (e : X ≃ Y) (he : ∀ (a : A) (x : X), e (a • x) = a • e x)
    (x₀ : X) (hd : ((p • e (p⁻¹ • x₀)) /ₛ e x₀ : A) = 1) :
    ∀ x, e (p • x) = p • e x := by
  have he₀ : p • e (p⁻¹ • x₀) = e x₀ := by
    calc
      _ = ((p • e (p⁻¹ • x₀)) /ₛ e x₀ : A) • e x₀ :=
        (sdiv_smul _ _).symm
      _ = _ := by rw [hd, one_smul]
  intro x
  let a : A := x /ₛ (p⁻¹ • x₀)
  have hx : a • (p⁻¹ • x₀) = x := sdiv_smul _ _
  calc
    e (p • x) = e (p • (a • (p⁻¹ • x₀))) :=
      congrArg (fun z : X => e (p • z)) hx.symm
    _ = e (φ a • x₀) := by rw [hX, smul_inv_smul]
    _ = φ a • e x₀ := he _ _
    _ = φ a • (p • e (p⁻¹ • x₀)) :=
      congrArg (fun z : Y => φ a • z) he₀.symm
    _ = p • (a • e (p⁻¹ • x₀)) := (hY a _).symm
    _ = p • e (a • (p⁻¹ • x₀)) :=
      congrArg (fun z : Y => p • z) (he a _).symm
    _ = p • e x := congrArg (fun z : X => p • e z) hx

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ]
  [IsSepClosure k κ] [IsSepClosed κ]
variable (E : IntermediateField k κ)
  [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
variable {X : Scheme} [ConnectedSpace X] (f : X ⟶ Spec (.of k))
variable {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)

/-- The canonical finite-base image kills the root quotient of the same
already selected radical, by literal membership in the same field E. -/
theorem quadraticScalar_rootQuotient_actual_canonicalBase_eq_one
    (β : κˣ) (hβE : (β : κ) ∈ E)
    (γ : π₁ᵉᵗ(arithmeticConstantFieldLift k E κ f xi)) :
    _root_.KummerTheory.rootQuotient (K := k) β
      (arithmeticFundamentalGroupHom k κ f xi
        (pointedFundamentalGroupHom
          ((FiniteEtale.pullback f).obj (originalConstantFieldCover k E)).hom
          (arithmeticConstantFieldLift k E κ f xi) xi
          (arithmeticConstantFieldLift_comp k E κ f xi) γ)) = 1 := by
  apply (_root_.KummerTheory.rootQuotient_eq_one_iff β _).mpr
  apply Units.ext
  exact arithmeticConstantFieldLift_arithmetic_image_fixes k E κ f xi γ
    (⟨(β : κ), hβE⟩ : E)

variable (W₁ W₂ : FiniteEtale X)
  [Torsor (rootsOfUnity 2 κ) ((fiber xi).obj W₁)]
  [Torsor (rootsOfUnity 2 κ) ((fiber xi).obj W₂)]
variable
  (h₁ : ∀ (p : π₁ᵉᵗ(xi)) (ζ : rootsOfUnity 2 κ) (x : (fiber xi).obj W₁),
    p • (ζ • x) = restrictRootsOfUnity
      (arithmeticFundamentalGroupHom k κ f xi p).toRingHom 2 ζ • (p • x))
  (h₂ : ∀ (p : π₁ᵉᵗ(xi)) (ζ : rootsOfUnity 2 κ) (y : (fiber xi).obj W₂),
    p • (ζ • y) = restrictRootsOfUnity
      (arithmeticFundamentalGroupHom k κ f xi p).toRingHom 2 ζ • (p • y))
  (e : (fiber xi).obj W₁ ≃ (fiber xi).obj W₂)
  (heμ : ∀ (ζ : rootsOfUnity 2 κ) x, e (ζ • x) = ζ • e x)
  (x₀ : (fiber xi).obj W₁) (β : κˣ) (hβE : (β : κ) ∈ E)
  (hdisp : ∀ p : π₁ᵉᵗ(xi),
    _root_.KummerTheory.rootQuotient (K := k) β
      (arithmeticFundamentalGroupHom k κ f xi p) =
        ((p • e (p⁻¹ • x₀)) /ₛ e x₀ : rootsOfUnity 2 κ).val)

include h₁ h₂ heμ hβE hdisp in
/-- Full equivariance of the unchanged original e on the actual canonical
finite-base image, retaining the original radical and displacement point. -/
theorem quadraticScalar_originalEquiv_actual_canonicalBase :
    let b := ((FiniteEtale.pullback f).obj (originalConstantFieldCover k E)).hom
    let xiE := arithmeticConstantFieldLift k E κ f xi
    let hp := arithmeticConstantFieldLift_comp k E κ f xi
    ∀ (γ : π₁ᵉᵗ(xiE)) (x : (fiber xi).obj W₁),
      e (pointedFundamentalGroupHom b xiE xi hp γ • x) =
        pointedFundamentalGroupHom b xiE xi hp γ • e x := by
  intro b xiE hp γ x
  let p := pointedFundamentalGroupHom b xiE xi hp γ
  have hr : _root_.KummerTheory.rootQuotient (K := k) β
      (arithmeticFundamentalGroupHom k κ f xi p) = 1 :=
    quadraticScalar_rootQuotient_actual_canonicalBase_eq_one k κ E f xi β hβE γ
  have hd : ((p • e (p⁻¹ • x₀)) /ₛ e x₀ : rootsOfUnity 2 κ) = 1 := by
    apply Subtype.ext
    exact (hdisp p).symm.trans hr
  exact canonical_equivariant_of_semilinear_displacement_eq_one p
    (restrictRootsOfUnity (arithmeticFundamentalGroupHom k κ f xi p).toRingHom 2)
    (h₁ p) (h₂ p) e heμ x₀ hd x

include h₁ h₂ heμ hβE hdisp in
/-- Full faithfulness constructs an actual isomorphism of the same two
pulled-back named covers and retains e at every original fibre point. -/
theorem quadraticScalar_actual_canonicalBase_coverIso
    [ConnectedSpace (((FiniteEtale.pullback f).obj (originalConstantFieldCover k E)).left)] :
    let b := ((FiniteEtale.pullback f).obj (originalConstantFieldCover k E)).hom
    let xiE := arithmeticConstantFieldLift k E κ f xi
    let hp := arithmeticConstantFieldLift_comp k E κ f xi
    ∃ j : (FiniteEtale.pullback b).obj W₁ ≅ (FiniteEtale.pullback b).obj W₂,
      ∀ x : (fiber xiE).obj ((FiniteEtale.pullback b).obj W₁),
        pointedPullbackFiberEquiv b xiE xi hp W₂ ((fiber xiE).map j.hom x) =
          e (pointedPullbackFiberEquiv b xiE xi hp W₁ x) := by
  intro b xiE hp
  let : ConnectedSpace ((𝟭 Scheme).obj
      ((FiniteEtale.pullback f).obj (originalConstantFieldCover k E)).left) :=
    inferInstanceAs (ConnectedSpace
      ((FiniteEtale.pullback f).obj (originalConstantFieldCover k E)).left)
  exact exists_pullbackCoverIso_of_pointed_equivariant b xiE xi hp W₁ W₂ e
    (quadraticScalar_originalEquiv_actual_canonicalBase
      k κ E f xi W₁ W₂ h₁ h₂ e heμ x₀ β hβE hdisp)

end AnabelianGeometry.WeightFiltration
