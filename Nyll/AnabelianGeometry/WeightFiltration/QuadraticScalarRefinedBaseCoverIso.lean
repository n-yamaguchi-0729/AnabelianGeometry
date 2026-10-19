/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticScalarFiniteBaseCoverIso

/-! # Retaining the same square transport after rationalizing its cusp lifts

Any intermediate field containing the original quadratic scalar field kills
the same displacement. Thus adjoining already selected cusp-root coordinates
retains the original e, x₀, scalar and radical in the actual cover isomorphism.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open scoped FintypeCatDiscrete

namespace AnabelianGeometry.WeightFiltration

local instance refinedQuadraticCoverIsoOverCategory (S : Scheme) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme) ⊤ S) :=
  AlgebraicGeometry.FiniteEtale.instCategory S

local instance refinedQuadraticCoverIsoHasPullbacksAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance refinedQuadraticCoverIsoStableUnderBaseChangeAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme)) h hf⟩

/-- On the original pointed arithmetic group, the actual finite base-change
image fixes the same scalar radical. No normalizer or quotient-label equality
is assumed: the single comparison conjugator is supplied by the existing owner. -/
theorem quadraticScalar_rootQuotient_actual_refinedBase_eq_one
    (k κ : Type) [Field k] [NumberField k] [Field κ] [Algebra k κ]
    [IsAlgClosure k κ]
    (a : kˣ) (β : κˣ)
    (hβ : β ^ 2 = Units.map (algebraMap k κ).toMonoidHom a)
    (E : IntermediateField k κ) (hE : quadraticScalarField k κ β ≤ E)
    (X : Scheme) (f : X ⟶ Spec (.of k))
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f) :
    let b := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k E))) f
    let xiE := scalarFiniteBasePoint k κ E X f xi
    let xiX := xi ≫ Limits.pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f
    let hp := scalarFiniteBasePoint_comp_snd k κ E X f xi
    ∀ γ : π₁ᵉᵗ(xiE),
      _root_.KummerTheory.rootQuotient (K := k) β
        (arithmeticFundamentalGroupHom k κ f xiX
          (pointedFundamentalGroupHom b xiE xiX hp γ)) = 1 := by
  intro b xiE xiX hp γ
  let : IsAlgClosed κ := IsAlgClosure.isAlgClosed k
  let : IsSepClosure k κ := inferInstance
  let : IsSepClosure E κ := ⟨inferInstance, inferInstance⟩
  let c := Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) f
  have hbase : b ≫ f = c ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) :=
    Limits.pullback.condition.symm
  obtain ⟨α, hα⟩ := arithmeticFundamentalGroupHom_fieldExtension_pointed_conjugate
    k E κ f c b hbase xiE xiX hp
  let p := arithmeticFundamentalGroupHom k κ f xiX
    (pointedFundamentalGroupHom b xiE xiX hp γ)
  have hmem : α (β : κ) ∈ E :=
    hE (quadraticScalarField_conjugate_mem k κ a β hβ α)
  have hfix : (arithmeticFundamentalGroupHom E κ c xiE γ).restrictScalars k
      (α (β : κ)) = α (β : κ) :=
    (arithmeticFundamentalGroupHom E κ c xiE γ).commutes ⟨α (β : κ), hmem⟩
  rw [hα γ] at hfix
  change α (p (α.symm (α (β : κ)))) = α (β : κ) at hfix
  rw [α.symm_apply_apply] at hfix
  apply (_root_.KummerTheory.rootQuotient_eq_one_iff β p).mpr
  apply Units.ext
  exact α.injective hfix


/-- Only semilinearity at the arithmetic element and the original torsor map
are needed to propagate trivial displacement from one point to every point. -/
private theorem refined_equivariant_of_semilinear_displacement_eq_one
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
theorem quadraticScalar_originalEquiv_actual_refinedBase
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
    (E : IntermediateField k κ) (hE : quadraticScalarField k κ β ≤ E)
    (hdisp : ∀ p : π₁ᵉᵗ(xi ≫ Limits.pullback.snd _ f),
      _root_.KummerTheory.rootQuotient (K := k) β
          (arithmeticFundamentalGroupHom k κ f (xi ≫ Limits.pullback.snd _ f) p) =
        ((p • e (p⁻¹ • x₀)) /ₛ e x₀ : rootsOfUnity 2 κ).val) :
    let b := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k E))) f
    let xiE := scalarFiniteBasePoint k κ E X f xi
    let xiX := xi ≫ Limits.pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f
    let hp := scalarFiniteBasePoint_comp_snd k κ E X f xi
    ∀ (γ : π₁ᵉᵗ(xiE)) (x : (fiber xiX).obj W₁),
      e (pointedFundamentalGroupHom b xiE xiX hp γ • x) =
        pointedFundamentalGroupHom b xiE xiX hp γ • e x := by
  intro b xiE xiX hp γ x
  let p := pointedFundamentalGroupHom b xiE xiX hp γ
  have hr : _root_.KummerTheory.rootQuotient (K := k) β
      (arithmeticFundamentalGroupHom k κ f xiX p) = 1 :=
    quadraticScalar_rootQuotient_actual_refinedBase_eq_one k κ a β hβ E hE X f xi γ
  have hd : ((p • e (p⁻¹ • x₀)) /ₛ e x₀ : rootsOfUnity 2 κ) = 1 := by
    apply Subtype.ext
    exact (hdisp p).symm.trans hr
  exact refined_equivariant_of_semilinear_displacement_eq_one p
    (restrictRootsOfUnity (arithmeticFundamentalGroupHom k κ f xiX p).toRingHom 2)
    (h₁ p) (h₂ p) e heμ x₀ hd x


/-- Killing the original quadratic scalar constructs an isomorphism of the
same two covers over its finite number field, with its original fiber map. -/
theorem quadraticScalar_actual_refinedBase_coverIso
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
    (E : IntermediateField k κ) (hE : quadraticScalarField k κ β ≤ E)
    (hdisp : ∀ p : π₁ᵉᵗ(xi ≫ Limits.pullback.snd _ f),
      _root_.KummerTheory.rootQuotient (K := k) β
          (arithmeticFundamentalGroupHom k κ f (xi ≫ Limits.pullback.snd _ f) p) =
        ((p • e (p⁻¹ • x₀)) /ₛ e x₀ : rootsOfUnity 2 κ).val) :
    let b := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k E))) f
    let xiE := scalarFiniteBasePoint k κ E X f xi
    let xiX := xi ≫ Limits.pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f
    let hp := scalarFiniteBasePoint_comp_snd k κ E X f xi
    ∃ j : (FiniteEtale.pullback b).obj W₁ ≅ (FiniteEtale.pullback b).obj W₂,
      ∀ x : (fiber xiE).obj ((FiniteEtale.pullback b).obj W₁),
        pointedPullbackFiberEquiv b xiE xiX hp W₂ ((fiber xiE).map j.hom x) =
          e (pointedPullbackFiberEquiv b xiE xiX hp W₁ x) := by
  intro b xiE xiX hp
  let : ConnectedSpace ↑(Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k E))) f) :=
    scalarFiniteBase_connectedSpace k κ E X f
  exact exists_pullbackCoverIso_of_pointed_equivariant b xiE xiX hp W₁ W₂ e
    (quadraticScalar_originalEquiv_actual_refinedBase
      k κ X f xi W₁ W₂ h₁ h₂ e heμ x₀ a β hβ E hE hdisp)


end AnabelianGeometry.WeightFiltration
