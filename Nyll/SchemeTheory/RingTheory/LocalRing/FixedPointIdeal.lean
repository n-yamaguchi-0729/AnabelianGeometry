/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# The local fixed-point ideal of a cotangent-contracting endomorphism

If an endomorphism of a Noetherian local ring induces the identity on the
residue field and sends the maximal ideal into its square, its actual
fixed-point equations generate the maximal ideal. Their quotient therefore
has length one. The generation statement follows from Nakayama, without
assuming an identification of a fixed-point quotient.
-/

@[expose] public section

namespace RingHom

variable {R : Type*} [CommRing R]

/-- The actual equations imposing equality of an endomorphism and the identity. -/
def fixedPointIdeal (f : R →+* R) : Ideal R :=
  Ideal.span (Set.range (fun x : R => f x - x))

end RingHom

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Cotangent contraction makes the fixed-point equations generate the maximal
ideal, provided the original residue endomorphism is the identity. -/
theorem fixedPointIdeal_eq_maximalIdeal (f : R →+* R)
    (hfg : (maximalIdeal R).FG)
    (hcontract : (maximalIdeal R).map f ≤ maximalIdeal R ^ 2)
    (hres : (residue R).comp f = residue R) :
    f.fixedPointIdeal = maximalIdeal R := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨x, rfl⟩
    apply (residue_eq_zero_iff (f x - x)).mp
    rw [map_sub, sub_eq_zero]
    exact congrArg (fun g : R →+* ResidueField R => g x) hres
  · apply Submodule.le_of_le_smul_of_le_jacobson_bot hfg (maximalIdeal_le_jacobson ⊥)
    intro x hx
    have hxrel : f x - x ∈ f.fixedPointIdeal :=
      Ideal.subset_span ⟨x, rfl⟩
    have hfx : f x ∈ maximalIdeal R • maximalIdeal R := by
      simpa only [Ideal.smul_eq_mul, pow_two] using
        hcontract (Ideal.mem_map_of_mem f hx)
    have hxsum : x = -(f x - x) + f x := by ring
    rw [hxsum]
    exact Submodule.add_mem_sup (f.fixedPointIdeal.neg_mem hxrel) hfx

/-- The local quotient cut out by the original fixed-point equations has
length one when the endomorphism is cotangent-contracting. -/
theorem length_quotient_fixedPointIdeal_eq_one [IsNoetherianRing R]
    (f : R →+* R)
    (hcontract : (maximalIdeal R).map f ≤ maximalIdeal R ^ 2)
    (hres : (residue R).comp f = residue R) :
    Module.length R (R ⧸ f.fixedPointIdeal) = 1 := by
  rw [fixedPointIdeal_eq_maximalIdeal f (IsNoetherian.noetherian _) hcontract hres]
  rw [Module.length_eq_one_iff, isSimpleModule_iff_quot_maximal]
  exact ⟨maximalIdeal R, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩

end IsLocalRing
