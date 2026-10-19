/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticBoundaryFieldInvariance
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticFieldComparisonConjugator

/-! # Quadratic Root Field Arbitrary Lift -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open EtaleFundamentalGroups
namespace AnabelianGeometry.WeightFiltration

variable (k κ : Type) [Field k] [CharZero k] [Field κ] [Algebra k κ]
  [IsAlgClosure k κ] [IsAlgClosed κ]
variable {ι : Type} (β : κˣ) (ρ : ι → κ)
variable (a : kˣ) (hβ : β ^ 2 = Units.map (algebraMap k κ).toMonoidHom a)
variable (v : ι → k) (hρ : ∀ i, ρ i ^ 2 = algebraMap k κ (v i))

include hβ hρ

theorem quadraticRootField_actual_lift_arithmetic_fixes
    {X Y : Scheme} (f : X ⟶ Spec (.of k))
    (c : Y ⟶ Spec (.of (quadraticBoundaryCoordinateField k κ β ρ)))
    (b : Y ⟶ X)
    (hb : b ≫ f = c ≫ Spec.map (CommRingCat.ofHom
      (algebraMap k (quadraticBoundaryCoordinateField k κ β ρ))))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (g : π₁ᵉᵗ(y)) :
    arithmeticFundamentalGroupHom k κ f (y ≫ b)
        (fundamentalGroupHom b y g) ∈
      (quadraticBoundaryCoordinateField k κ β ρ).fixingSubgroup := by
  let E := quadraticBoundaryCoordinateField k κ β ρ
  let hAlgE : Algebra.IsAlgebraic E κ :=
    Algebra.IsAlgebraic.tower_top (K := k) (L := E) (A := κ)
  let hSepE : IsSepClosure E κ :=
    ⟨inferInstance, hAlgE.isSeparable_of_perfectField⟩
  let δ := fieldExtensionComparisonConjugator k E κ (y ≫ c)
  let γ := arithmeticFundamentalGroupHom k κ f (y ≫ b)
    (fundamentalGroupHom b y g)
  have heq : (arithmeticFundamentalGroupHom E κ c y g).restrictScalars k =
      δ * γ * δ⁻¹ :=
    fieldExtensionComparisonConjugator_arithmetic k E κ f c b hb y g
  have hfix : δ * γ * δ⁻¹ ∈ E.fixingSubgroup := by
    rw [← heq, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (arithmeticFundamentalGroupHom E κ c y g).commutes (⟨x, hx⟩ : E)
  exact (quadraticBoundaryCoordinateField_conj_mem_fixingSubgroup_iff
    k κ β ρ a hβ v hρ δ γ).mp hfix

theorem quadraticRootField_actual_lift_rootQuotient_eq_one
    {X Y : Scheme} (f : X ⟶ Spec (.of k))
    (c : Y ⟶ Spec (.of (quadraticBoundaryCoordinateField k κ β ρ)))
    (b : Y ⟶ X)
    (hb : b ≫ f = c ≫ Spec.map (CommRingCat.ofHom
      (algebraMap k (quadraticBoundaryCoordinateField k κ β ρ))))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (g : π₁ᵉᵗ(y)) :
    _root_.KummerTheory.rootQuotient (K := k) β
      (arithmeticFundamentalGroupHom k κ f (y ≫ b)
        (fundamentalGroupHom b y g)) = 1 := by
  apply (_root_.KummerTheory.rootQuotient_eq_one_iff β _).mpr
  apply Units.ext
  have hfix := quadraticRootField_actual_lift_arithmetic_fixes
    k κ β ρ a hβ v hρ f c b hb y g
  exact ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hfix) (β : κ)
    (scalar_mem_quadraticBoundaryCoordinateField k κ β ρ)

theorem quadraticRootField_actual_lift_scalarEquivariance
    {X Y : Scheme} (f : X ⟶ Spec (.of k))
    (c : Y ⟶ Spec (.of (quadraticBoundaryCoordinateField k κ β ρ)))
    (b : Y ⟶ X)
    (hb : b ≫ f = c ≫ Spec.map (CommRingCat.ofHom
      (algebraMap k (quadraticBoundaryCoordinateField k κ β ρ))))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    {S T : Type*} [Torsor (rootsOfUnity 2 κ) S] [Torsor (rootsOfUnity 2 κ) T]
    [MulAction (π₁ᵉᵗ(y ≫ b)) S] [MulAction (π₁ᵉᵗ(y ≫ b)) T]
    (hS : ∀ (p : π₁ᵉᵗ(y ≫ b)) (ζ : rootsOfUnity 2 κ) (x : S),
      p • (ζ • x) = restrictRootsOfUnity
        (arithmeticFundamentalGroupHom k κ f (y ≫ b) p).toRingHom 2 ζ • (p • x))
    (hT : ∀ (p : π₁ᵉᵗ(y ≫ b)) (ζ : rootsOfUnity 2 κ) (x : T),
      p • (ζ • x) = restrictRootsOfUnity
        (arithmeticFundamentalGroupHom k κ f (y ≫ b) p).toRingHom 2 ζ • (p • x))
    (e : S ≃ T) (he : ∀ (ζ : rootsOfUnity 2 κ) x, e (ζ • x) = ζ • e x)
    (x₀ : S)
    (hdisp : ∀ p : π₁ᵉᵗ(y ≫ b),
      _root_.KummerTheory.rootQuotient (K := k) β
        (arithmeticFundamentalGroupHom k κ f (y ≫ b) p) =
          ((p • e (p⁻¹ • x₀)) /ₛ e x₀ : rootsOfUnity 2 κ).val)
    (g : π₁ᵉᵗ(y)) (x : S) :
    e (fundamentalGroupHom b y g • x) = fundamentalGroupHom b y g • e x := by
  let p := fundamentalGroupHom b y g
  let φ := restrictRootsOfUnity
    (arithmeticFundamentalGroupHom k κ f (y ≫ b) p).toRingHom 2
  have hd : ((p • e (p⁻¹ • x₀)) /ₛ e x₀ : rootsOfUnity 2 κ) = 1 := by
    apply Subtype.ext
    exact (hdisp p).symm.trans
      (quadraticRootField_actual_lift_rootQuotient_eq_one
        k κ β ρ a hβ v hρ f c b hb y g)
  have he₀ : p • e (p⁻¹ • x₀) = e x₀ := by
    calc
      _ = ((p • e (p⁻¹ • x₀)) /ₛ e x₀ : rootsOfUnity 2 κ) • e x₀ :=
        (sdiv_smul _ _).symm
      _ = e x₀ := by rw [hd, one_smul]
  let ζ : rootsOfUnity 2 κ := x /ₛ (p⁻¹ • x₀)
  have hx : ζ • (p⁻¹ • x₀) = x := sdiv_smul _ _
  calc
    e (p • x) = e (p • (ζ • (p⁻¹ • x₀))) :=
      congrArg (fun z : S => e (p • z)) hx.symm
    _ = e (φ ζ • x₀) := by rw [hS, smul_inv_smul]
    _ = φ ζ • e x₀ := he _ _
    _ = φ ζ • (p • e (p⁻¹ • x₀)) :=
      congrArg (fun z : T => φ ζ • z) he₀.symm
    _ = p • (ζ • e (p⁻¹ • x₀)) := (hT p ζ _).symm
    _ = p • e (ζ • (p⁻¹ • x₀)) :=
      congrArg (fun z : T => p • z) (he ζ _).symm
    _ = p • e x := congrArg (fun z : S => p • e z) hx

end AnabelianGeometry.WeightFiltration
