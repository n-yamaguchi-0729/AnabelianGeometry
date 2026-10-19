/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Cohomology.KernelTorsorIsom
import Nyll.GaloisCohomology.Kummer.Concrete.ContinuousKummerScalar

/-!
# Pointwise cusp ratios from the same arithmetic Isom

The corrected source and target specialization coordinates scale by their
fixed coefficient labels. Only the chosen arithmetic element needs to agree
with the original decomposition action at the two cusps. The same Isom and
its displacement at the original point are retained.
-/

noncomputable section
namespace EtaleFundamentalGroups.Cohomology

private theorem KernelTorsorIso.displacement_smul_apply
    {P G A X Y : Type*} [Group P] [Group G] [CommGroup A]
    [MulDistribMulAction G A] [Torsor A X] [Torsor A Y]
    [MulAction P X] [MulAction P Y]
    (q : P →* G)
    (hX : ∀ (p : P) (a : A) (x : X), p • (a • x) = (q p • a) • (p • x))
    (hY : ∀ (p : P) (a : A) (y : Y), p • (a • y) = (q p • a) • (p • y))
    (e : KernelTorsorIso (X := X) (Y := Y) q A) (x₀ x : X) (p : P) :
    p • e.val x =
      ((p • e.val (p⁻¹ • x₀)) /ₛ e.val x₀ : A) • e.val (p • x) := by
  let c : A := (p • e.val (p⁻¹ • x₀)) /ₛ e.val x₀
  have he : kernelTorsorIsoConjugate q hX hY p e =
      kernelTorsorIsoTranslate q hY c e := by
    apply KernelTorsorIso.ext_at q _ _ x₀
    exact (sdiv_smul _ _).symm
  have hx := congrArg (fun f : KernelTorsorIso (X := X) (Y := Y) q A =>
    f.val (p • x)) he
  change p • e.val (p⁻¹ • (p • x)) = c • e.val (p • x) at hx
  simpa only [inv_smul_smul] using hx

/-- Local corrected coordinates turn the displacement of the original Isom
into the exact radical-ratio relation, with both fixed labels visible. -/
theorem KernelTorsorIso.cusp_coordinate_ratio_with_kernel_conjugator
    {k κ : Type} {P X Y : Type*} [Field k] [Field κ] [Algebra k κ] [Group P]
    (n : ℕ) [MulDistribMulAction Gal(κ/k) (rootsOfUnity n κ)]
    [Torsor (rootsOfUnity n κ) X] [Torsor (rootsOfUnity n κ) Y]
    [MulAction P X] [MulAction P Y]
    (q : P →* Gal(κ/k))
    (hX : ∀ (p : P) (a : rootsOfUnity n κ) (x : X),
      p • (a • x) = (q p • a) • (p • x))
    (hY : ∀ (p : P) (a : rootsOfUnity n κ) (y : Y),
      p • (a • y) = (q p • a) • (p • y))
    (e : KernelTorsorIso (X := X) (Y := Y) q (rootsOfUnity n κ))
    (x₀ x : X) (p γ : P) (hγ : q γ = 1) (αs αt : Gal(κ/k))
    (S : X → κ) (T : Y → κ)
    (hS : ∀ (ζ : rootsOfUnity n κ) z, S (ζ • z) = αs (ζ.val : κ) * S z)
    (hT : ∀ (ζ : rootsOfUnity n κ) z, T (ζ • z) = αt (ζ.val : κ) * T z)
    (hSp : S (p • x) = q p (S x))
    (hTp : T ((γ * p * γ⁻¹) • (γ • e.val x)) = q p (T (γ • e.val x)))
    (hS0 : S x ≠ 0) (hT0 : T (γ • e.val x) ≠ 0) :
    let c : rootsOfUnity n κ := (p • e.val (p⁻¹ • x₀)) /ₛ e.val x₀
    q p (T (γ • e.val x)) / T (γ • e.val x) =
      αt (c.val : κ) * αt (αs.symm (q p (S x) / S x)) := by
  intro c
  let ζ : rootsOfUnity n κ := (p • x) /ₛ x
  have hζ : ζ • x = p • x := sdiv_smul _ _
  have hsource : q p (S x) / S x = αs (ζ.val : κ) := by
    rw [← hSp, ← hζ, hS, mul_div_cancel_right₀ _ hS0]
  have hmove : (γ * p * γ⁻¹) • (γ • e.val x) =
      c • (ζ • (γ • e.val x)) := by
    calc
      _ = γ • (p • e.val x) := by simp only [mul_smul, inv_smul_smul]
      _ = γ • (c • e.val (p • x)) :=
        congrArg (fun y : Y => γ • y)
          (KernelTorsorIso.displacement_smul_apply q hX hY e x₀ x p)
      _ = c • (γ • e.val (p • x)) := by rw [hY, hγ, one_smul]
      _ = c • (ζ • (γ • e.val x)) := by
        rw [← hζ, e.property.1, hY, hγ, one_smul]
  have htarget : q p (T (γ • e.val x)) =
      αt (c.val : κ) * (αt (ζ.val : κ) * T (γ • e.val x)) := by
    rw [← hTp, hmove, hT, hT]
  rw [htarget, hsource, αs.symm_apply_apply]
  rw [← mul_assoc, mul_div_cancel_right₀ _ hT0]

/-- Changing the chosen point in one actual cusp fiber only multiplies its
corrected root coordinate by a root of unity; its nth power is unchanged. -/
theorem cusp_coordinate_pow_independent_of_fiber_point
    {k κ Y : Type} [Field k] [Field κ] [Algebra k κ]
    (n : ℕ) [Torsor (rootsOfUnity n κ) Y]
    (α : Gal(κ/k)) (T : Y → κ)
    (hT : ∀ (ζ : rootsOfUnity n κ) y, T (ζ • y) = α (ζ.val : κ) * T y)
    (y z : Y) : (T y) ^ n = (T z) ^ n := by
  let ζ : rootsOfUnity n κ := y /ₛ z
  have hζ : ζ • z = y := sdiv_smul _ _
  have hz : (ζ.val : κ) ^ n = 1 :=
    congrArg Units.val ((mem_rootsOfUnity n ζ.val).mp ζ.property)
  rw [← hζ, hT, mul_pow, ← map_pow, hz, map_one, one_mul]

end EtaleFundamentalGroups.Cohomology
