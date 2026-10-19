/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticScalarFiniteBase

/-! # The original quadratic Isom witness over its actual finite scalar field

The scalar and its radical are the ones in the original arithmetic displacement.
The actual pointed base-change map fixes that radical, so the original fiber
map is equivariant on its image. No replacement of the geometric comparison,
no new choice of scalar, and no identification of lifted cusps is made here.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open scoped FintypeCatDiscrete

namespace AnabelianGeometry.WeightFiltration

/-- Only semilinearity at the arithmetic element and the original torsor map
are needed to propagate trivial displacement from one point to every point. -/
private theorem equivariant_of_semilinear_displacement_eq_one
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

/-- The original arithmetic fiber equivalence is equivariant under the actual
finite-base image, for the same scalar radical already chosen by descent. -/
theorem quadraticScalar_originalEquiv_actual_finiteBase
    (k κ : Type) [Field k] [NumberField k] [Field κ] [Algebra k κ]
    [IsAlgClosure k κ]
    (X : Scheme) (f : X ⟶ Spec (.of k))
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
        ((p • e (p⁻¹ • x₀)) /ₛ e x₀ : rootsOfUnity 2 κ).val) :
    let E := quadraticScalarField k κ β
    let b := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k E))) f
    let xiE := scalarFiniteBasePoint k κ E X f xi
    let xiX := xi ≫ Limits.pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f
    let hp := scalarFiniteBasePoint_comp_snd k κ E X f xi
    ∀ (γ : π₁ᵉᵗ(xiE)) (x : (fiber xiX).obj W₁),
      e (pointedFundamentalGroupHom b xiE xiX hp γ • x) =
        pointedFundamentalGroupHom b xiE xiX hp γ • e x := by
  intro E b xiE xiX hp γ x
  let p := pointedFundamentalGroupHom b xiE xiX hp γ
  have hr : _root_.KummerTheory.rootQuotient (K := k) β
      (arithmeticFundamentalGroupHom k κ f xiX p) = 1 :=
    quadraticScalar_rootQuotient_actual_finiteBase_eq_one k κ a β hβ X f xi γ
  have hd : ((p • e (p⁻¹ • x₀)) /ₛ e x₀ : rootsOfUnity 2 κ) = 1 := by
    apply Subtype.ext
    exact (hdisp p).symm.trans hr
  exact equivariant_of_semilinear_displacement_eq_one p
    (restrictRootsOfUnity (arithmeticFundamentalGroupHom k κ f xiX p).toRingHom 2)
    (h₁ p) (h₂ p) e heμ x₀ hd x

end AnabelianGeometry.WeightFiltration
