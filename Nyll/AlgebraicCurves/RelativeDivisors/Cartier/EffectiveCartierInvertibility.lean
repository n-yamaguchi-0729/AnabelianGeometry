/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.Cartier
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.EffectiveCartierIdeal
public import Nyll.SchemeTheory.Divisors.Basic
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.Defs

/-!
# The original invertible-ideal condition for an effective Cartier divisor

An affine Cartier equation restricts to the affine basic open of `1`,
where the localization map preserves its non-zero-divisor property.
Thus the two existing local definitions apply to exactly the same ideal
sheaves. This allows their actual invertible modules to be used with the
original cohomological Cartier classes.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- An effective Cartier ideal satisfies the original affine-basic-open
invertibility condition, using the same local equations. -/
theorem IsEffectiveCartier.isInvertible
    {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsEffectiveCartier) :
    I.IsInvertible := by
  intro x
  obtain ⟨U, hxU, f, hf, hIf⟩ := hI x
  let h : X.basicOpen (1 : Γ(X, U.1)) ≤ U.1 := X.basicOpen_le 1
  let g : Γ(X, X.affineBasicOpen (1 : Γ(X, U.1))) :=
    X.presheaf.map (homOfLE h).op f
  have hf' : f ∈ nonZeroDivisors Γ(X, U.1) :=
    mem_nonZeroDivisors_iff.mpr
      ⟨fun a ha => hf.left (ha.trans (mul_zero f).symm),
       fun a ha => hf.right (ha.trans (zero_mul f).symm)⟩
  have hg : g ∈ nonZeroDivisors Γ(X, X.affineBasicOpen (1 : Γ(X, U.1))) := by
    have := U.2.isLocalization_basicOpen (1 : Γ(X, U.1))
    exact IsLocalization.nonZeroDivisors_le_comap
      (M := Submonoid.powers (1 : Γ(X, U.1)))
      (S := Γ(X, X.basicOpen (1 : Γ(X, U.1)))) hf'
  refine ⟨U, 1, ?_, g, hg, ?_⟩
  · simpa only [Scheme.basicOpen_one] using hxU
  · rw [← I.map_ideal (U := X.affineBasicOpen (1 : Γ(X, U.1))) (V := U) h,
      hIf, Ideal.map_span, Set.image_singleton]
    rfl

/-- The original ideal sheaf is unchanged when passing between the
effective Cartier and invertible-ideal local conditions. -/
theorem isEffectiveCartier_iff_isInvertible
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    I.IsEffectiveCartier ↔ I.IsInvertible :=
  ⟨IsEffectiveCartier.isInvertible, IsInvertible.isEffectiveCartier⟩

end AlgebraicGeometry.Scheme.IdealSheafData
