/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Places.Evaluation.HasValueIffMemEqOrOrdSubPos
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Order.Filter.Cofinite

/-!
# Additivity from values on multiplicative generators

The last step of Tamagawa's additive reconstruction can be performed directly
on curve places. A rational function vanishing at cofinitely many distinct
places is zero. Consequently, compatibility of values on multiplicative
generators propagates to every rational function and implies additivity.

This is the final algebraic step, not the full reconstruction theorem: the
minimal-pencil generation and the value comparisons are separate inputs to
be constructed from the valuation and principal-unit data.
-/

@[expose] public section

namespace AnabelianGeometry.FunctionField

open AlgebraicCurve Filter

theorem eq_of_eventually_same_value
    {K F ι : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Infinite ι] (v : ι → Place K F) (hv : Function.Injective v) {f g : F}
    (h : ∀ᶠ i in cofinite, ∃ c : K, (v i).HasValue f c ∧ (v i).HasValue g c) :
    f = g := by
  classical
  by_contra hne
  have hfg : f - g ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨D, hD, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) (f - g) hfg
  have hfinite : (v ⁻¹' (↑D.support : Set (Place K F))).Finite :=
    Set.Finite.preimage hv.injOn D.support.finite_toSet
  obtain ⟨i, ⟨c, hf, hg⟩, hi⟩ :=
    (h.and hfinite.eventually_cofinite_notMem).exists
  have hz : (v i).HasValue (f - g) (0 : K) := by
    simpa only [sub_self] using hf.sub hg
  have hpos : 0 < (v i).ord (f - g) := by
    have hh := ((v i).hasValue_iff_mem_and_eq_or_ord_sub_pos (f - g) 0).mp hz
    simp only [map_zero, sub_zero] at hh
    exact hh.2.resolve_left hfg
  apply hi
  change v i ∈ D.support
  apply Finsupp.mem_support_iff.mpr
  rw [hD (v i)]
  exact ne_of_gt hpos

/-- A multiplicative map of curve function fields is additive if its values on
a multiplicatively generating set agree, away from finitely many places, with
one fixed map of constant fields. The exceptional set may depend on a generator.
-/
theorem map_add_of_multiplicative_generators
    {K₁ K₂ F₁ F₂ : Type*} [Field K₁] [Field K₂] [Field F₁] [Field F₂]
    [Algebra K₁ F₁] [Algebra K₂ F₂] [IsCurveOver K₂ F₂]
    [Infinite (Place K₁ F₁)]
    (φ : F₁ →*₀ F₂) (σ : K₁ →+* K₂)
    (v : Place K₁ F₁ → Place K₂ F₂) (hv : Function.Injective v)
    (S : Set F₁) (hS : Submonoid.closure S = ⊤)
    (hvalues : ∀ x ∈ S, ∀ᶠ P in cofinite,
      ∃ c : K₁, P.HasValue x c ∧ (v P).HasValue (φ x) (σ c))
    (a b : F₁) : φ (a + b) = φ a + φ b := by
  let E : Submonoid F₁ :=
    { carrier := {x | ∀ᶠ P in cofinite,
        ∃ c : K₁, P.HasValue x c ∧ (v P).HasValue (φ x) (σ c)}
      one_mem' := by
        change ∀ᶠ P in cofinite, ∃ c : K₁, P.HasValue (1 : F₁) c ∧
          (v P).HasValue (φ 1) (σ c)
        apply Filter.Eventually.of_forall
        intro P
        refine ⟨1, P.hasValue_one, ?_⟩
        rw [map_one, map_one]
        exact (v P).hasValue_one
      mul_mem' := by
        intro x y hx hy
        change ∀ᶠ P in cofinite, ∃ c : K₁, P.HasValue x c ∧ (v P).HasValue (φ x) (σ c) at hx
        change ∀ᶠ P in cofinite, ∃ c : K₁, P.HasValue y c ∧ (v P).HasValue (φ y) (σ c) at hy
        change ∀ᶠ P in cofinite, ∃ c : K₁, P.HasValue (x * y) c ∧
          (v P).HasValue (φ (x * y)) (σ c)
        exact (hx.and hy).mono fun P ⟨⟨c, hxc, hφxc⟩, ⟨d, hyd, hφyd⟩⟩ => by
          refine ⟨c * d, hxc.mul hyd, ?_⟩
          rw [map_mul, map_mul]
          exact hφxc.mul hφyd }
  have hclosure : Submonoid.closure S ≤ E :=
    Submonoid.closure_le.mpr fun x hx => hvalues x hx
  have hall (x : F₁) : ∀ᶠ P in cofinite,
      ∃ c : K₁, P.HasValue x c ∧ (v P).HasValue (φ x) (σ c) := by
    apply hclosure
    rw [hS]
    exact Submonoid.mem_top x
  apply eq_of_eventually_same_value v hv
  exact ((hall (a + b)).and ((hall a).and (hall b))).mono
    fun P ⟨⟨c, hab, hφab⟩, ⟨⟨d, ha, hφa⟩, ⟨e, hb, hφb⟩⟩⟩ => by
      have hc : c = d + e := hab.unique (ha.add hb)
      refine ⟨σ c, hφab, ?_⟩
      rw [hc, map_add]
      exact hφa.add hφb

end AnabelianGeometry.FunctionField
