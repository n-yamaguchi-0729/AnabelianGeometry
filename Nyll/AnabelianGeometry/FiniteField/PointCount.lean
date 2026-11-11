/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.JacobianVarieties.Kummer.FiniteFieldCurveTrace
public import Nyll.SchemeTheory.Morphisms.FrobeniusFixedSchemePoints

/-!
# Point-count consequences of an actual Frobenius-equivariant H¹ comparison

These deductions use the smooth proper curve trace formula at the first
Frobenius power. The comparison here is between the actual classical rational
ℓ-adic cohomology groups of the two geometric curves; the reconstruction
modules supply the comparisons arising from mixed arithmetic fundamental
groups. Properness is required here. Affine boundary contributions are
handled separately through inertia.

Positivity is stated in `ℕ`, never by inventing an order on the ℓ-adic field.
No finiteness of rational points is silently inferred from `Nat.card`. For
schemes in `Type`, the existing geometric fixed-point finiteness theorem also
supplies finiteness, and hence the criterion in terms of nonemptiness itself.

-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits NeronModelInfra
open EtaleCohomology.Classical EtaleCohomology.FiniteFieldCurve

namespace AnabelianGeometry.FiniteField

section General

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
  [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
  (ℓ p : ℕ) [Fact ℓ.Prime] [CharP k p]
  (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]

local notation "cX" => (X ↘ Spec (CommRingCat.of k))
local notation "cY" => (Y ↘ Spec (CommRingCat.of k))
local notation "XΩ" => pullback cX (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
local notation "YΩ" => pullback cY (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
local notation "PX" => SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) cX
local notation "PY" => SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) cY

omit [IsAlgClosed Ω] [CharP k p] in
/-- Frobenius equivariance on actual cohomology implies equality of its trace. -/
theorem frobeniusTrace_eq_of_equivariant
    (e : rationalEllAdicCohomology ℓ XΩ 1 ≃ₗ[ℚ_[ℓ]] rationalEllAdicCohomology ℓ YΩ 1)
    (he : ∀ x, e (rationalEllAdicFrobenius ℓ k Ω X 1 x) =
      rationalEllAdicFrobenius ℓ k Ω Y 1 (e x)) :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ XΩ 1)
        (rationalEllAdicFrobenius ℓ k Ω X 1) =
      LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ YΩ 1)
        (rationalEllAdicFrobenius ℓ k Ω Y 1) := by
  have hc : e.conj (rationalEllAdicFrobenius ℓ k Ω X 1) =
      rationalEllAdicFrobenius ℓ k Ω Y 1 := by
    apply LinearMap.ext
    intro y
    change e (rationalEllAdicFrobenius ℓ k Ω X 1 (e.symm y)) = _
    rw [he, e.apply_symm_apply]
  rw [← hc]
  exact (LinearMap.trace_conj' (rationalEllAdicFrobenius ℓ k Ω X 1) e).symm

variable [IsProper (X ↘ Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k))]
  [IsProper (Y ↘ Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of k))]
  [GeometricallyConnected (Y ↘ Spec (CommRingCat.of k))]

/-- Equal geometric Frobenius traces give equal natural point counts. -/
theorem rationalPointCount_eq_of_frobeniusTrace_eq (hℓp : ℓ ≠ p)
    (htrace : LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ XΩ 1)
        (rationalEllAdicFrobenius ℓ k Ω X 1) =
      LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ YΩ 1)
        (rationalEllAdicFrobenius ℓ k Ω Y 1)) :
    Nat.card PX = Nat.card PY := by
  apply Nat.cast_injective (R := ℚ_[ℓ])
  rw [smoothProperCurve_lefschetz k Ω ℓ p X hℓp,
    smoothProperCurve_lefschetz k Ω ℓ p Y hℓp, htrace]

/-- A Frobenius-equivariant comparison yields equality of the actual point counts. -/
theorem rationalPointCount_eq_of_equivariant (hℓp : ℓ ≠ p)
    (e : rationalEllAdicCohomology ℓ XΩ 1 ≃ₗ[ℚ_[ℓ]] rationalEllAdicCohomology ℓ YΩ 1)
    (he : ∀ x, e (rationalEllAdicFrobenius ℓ k Ω X 1 x) =
      rationalEllAdicFrobenius ℓ k Ω Y 1 (e x)) :
    Nat.card PX = Nat.card PY :=
  rationalPointCount_eq_of_frobeniusTrace_eq k Ω ℓ p X Y hℓp
    (frobeniusTrace_eq_of_equivariant k Ω ℓ X Y e he)

/-- The positive integral point-count criterion, expressed without ordering `ℚ_[ℓ]`. -/
theorem rationalPointCount_pos_iff_frobeniusTrace_ne (hℓp : ℓ ≠ p) :
    0 < Nat.card PX ↔
      LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ XΩ 1)
        (rationalEllAdicFrobenius ℓ k Ω X 1) ≠ 1 + (Fintype.card k : ℚ_[ℓ]) := by
  have h := smoothProperCurve_lefschetz k Ω ℓ p X hℓp
  constructor
  · intro hn ht
    rw [ht, sub_self] at h
    have hz : Nat.card PX = 0 := Nat.cast_injective (R := ℚ_[ℓ])
      (h.trans (Nat.cast_zero (R := ℚ_[ℓ])).symm)
    exact (Nat.ne_of_gt hn) hz
  · intro ht
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, Nat.cast_zero] at h
    exact ht (sub_eq_zero.mp h.symm).symm

/-- Nonzero Lefschetz point count supplies an actual rational scheme point. -/
theorem nonempty_rationalPoints_of_frobeniusTrace_ne (hℓp : ℓ ≠ p)
    (htrace : LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ XΩ 1)
      (rationalEllAdicFrobenius ℓ k Ω X 1) ≠ 1 + (Fintype.card k : ℚ_[ℓ])) :
    Nonempty PX :=
  (Nat.card_pos_iff.mp
    ((rationalPointCount_pos_iff_frobeniusTrace_ne k Ω ℓ p X hℓp).mpr htrace)).1

/-- Positivity transfers through an equivariant H¹ comparison and yields a point. -/
theorem nonempty_rationalPoints_of_equivariant (hℓp : ℓ ≠ p)
    (e : rationalEllAdicCohomology ℓ XΩ 1 ≃ₗ[ℚ_[ℓ]] rationalEllAdicCohomology ℓ YΩ 1)
    (he : ∀ x, e (rationalEllAdicFrobenius ℓ k Ω X 1 x) =
      rationalEllAdicFrobenius ℓ k Ω Y 1 (e x))
    (hX : 0 < Nat.card PX) : Nonempty PY := by
  have hcard := rationalPointCount_eq_of_equivariant k Ω ℓ p X Y hℓp e he
  exact (Nat.card_pos_iff.mp (hcard ▸ hX)).1

end General

section FiniteRationalPoints

/-- Actual rational points of a quasi-compact finite-type scheme over a finite
field form a finite type. This reuses geometric fixed-point finiteness at the
identity coefficient automorphism. -/
theorem finite_rationalPoints
    (k : Type uGeom) [Field k] [Finite k] (X : Scheme.{uGeom}) [CompactSpace X]
    (c : X ⟶ Spec (.of k)) [LocallyOfFiniteType c] :
    Finite (SchemeHomOver (𝟙 (Spec (.of k))) c) := by
  have hbase : Spec.algebraMap k k = 𝟙 (Spec (.of k)) := by
    change Spec.map (CommRingCat.ofHom (algebraMap k k)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hσ : Spec.map (CommRingCat.ofHom (AlgEquiv.refl : k ≃ₐ[k] k).toRingHom) =
      𝟙 (Spec (.of k)) := by
    change Spec.map (CommRingCat.ofHom (RingHom.id k)) = _
    rw [CommRingCat.ofHom_id, Spec.map_id]
  have hfixed : Finite {x : SchemeHomOver (Spec.algebraMap k k) c //
      Spec.map (CommRingCat.ofHom (AlgEquiv.refl : k ≃ₐ[k] k).toRingHom) ≫ x.val = x.val} :=
    WeightFiltration.finite_fixed_scheme_points k k (AlgEquiv.refl : k ≃ₐ[k] k) X c
  rw [hbase] at hfixed
  have : Finite {x : SchemeHomOver (𝟙 (Spec (.of k))) c // x.val = x.val} := by
    simpa only [hσ, Category.id_comp] using hfixed
  let send (x : SchemeHomOver (𝟙 (Spec (.of k))) c) :
      {x : SchemeHomOver (𝟙 (Spec (.of k))) c // x.val = x.val} := ⟨x, rfl⟩
  apply Finite.of_injective send
  intro x y h
  exact congrArg Subtype.val h

variable (k Ω : Type uGeom) [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
  [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
  (ℓ p : ℕ) [Fact ℓ.Prime] [CharP k p]
  (X Y : Scheme.{uGeom}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]

local notation "cX" => (X ↘ Spec (CommRingCat.of k))
local notation "cY" => (Y ↘ Spec (CommRingCat.of k))
local notation "XΩ" => pullback cX (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
local notation "YΩ" => pullback cY (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
local notation "PX" => SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) cX
local notation "PY" => SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) cY

variable [IsProper (X ↘ Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k))]
  [IsProper (Y ↘ Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of k))]
  [GeometricallyConnected (Y ↘ Spec (CommRingCat.of k))]

/-- Point existence is equivalent to the nonvanishing of the actual Lefschetz
count, with finiteness proved from the curve's geometry. -/
theorem nonempty_rationalPoints_iff_frobeniusTrace_ne (hℓp : ℓ ≠ p) :
    Nonempty PX ↔
      LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ XΩ 1)
        (rationalEllAdicFrobenius ℓ k Ω X 1) ≠ 1 + (Fintype.card k : ℚ_[ℓ]) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace cX
  have : Finite PX := finite_rationalPoints k X cX
  have hp : Nonempty PX ↔ 0 < Nat.card PX := by
    constructor
    · intro h
      exact Nat.card_pos_iff.mpr ⟨h, inferInstance⟩
    · intro h
      exact (Nat.card_pos_iff.mp h).1
  exact hp.trans (rationalPointCount_pos_iff_frobeniusTrace_ne k Ω ℓ p X hℓp)

/-- An actual equivariant H¹ comparison preserves existence of rational points. -/
theorem nonempty_rationalPoints_iff_of_equivariant (hℓp : ℓ ≠ p)
    (e : rationalEllAdicCohomology ℓ XΩ 1 ≃ₗ[ℚ_[ℓ]] rationalEllAdicCohomology ℓ YΩ 1)
    (he : ∀ x, e (rationalEllAdicFrobenius ℓ k Ω X 1 x) =
      rationalEllAdicFrobenius ℓ k Ω Y 1 (e x)) :
    Nonempty PX ↔ Nonempty PY := by
  rw [nonempty_rationalPoints_iff_frobeniusTrace_ne k Ω ℓ p X hℓp,
    nonempty_rationalPoints_iff_frobeniusTrace_ne k Ω ℓ p Y hℓp,
    frobeniusTrace_eq_of_equivariant k Ω ℓ X Y e he]

end FiniteRationalPoints

end AnabelianGeometry.FiniteField
