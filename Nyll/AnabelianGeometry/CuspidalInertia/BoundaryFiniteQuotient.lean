/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Algebra.Group.Pi.Basic

/-!
# Finite-coordinate detection in the diagonal boundary quotient

A finite discrete character detecting n-th powers on the source also detects
n-th powers after quotienting a finite product by its diagonal. Distinct
boundary labels remain distinct at any coefficient whose square is not one,
including the two-label case.
-/

namespace AnabelianGeometry.CuspidalInertia

/-- Powers form an open subset of the reduced boundary group whenever they
are the kernel of a discrete character of the coefficient group. -/
theorem isOpen_pow_diagonalQuotient
    {R H S : Type*}
    [CommGroup R] [TopologicalSpace R]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [DiscreteTopology H] [Finite S]
    (s0 : S) (π : R →* H) (hπ : Continuous π) (n : ℕ)
    (hker : ∀ r : R, π r = 1 ↔ ∃ y : R, y ^ n = r) :
    IsOpen {b : (S → R) ⧸ (Pi.constMonoidHom S R).range |
      ∃ c, c ^ n = b} := by
  classical
  let D : Subgroup (S → R) := (Pi.constMonoidHom S R).range
  let B := (S → R) ⧸ D
  let δ : (S → R) →* (S → H) :=
    { toFun := fun x s => π (x s) * (π (x s0))⁻¹
      map_one' := by
        funext s
        change π (1 : R) * (π (1 : R))⁻¹ = 1
        exact mul_inv_cancel (π 1)
      map_mul' := by
        intro x y
        funext s
        change π (x s * y s) * (π (x s0 * y s0))⁻¹ =
          (π (x s) * (π (x s0))⁻¹) * (π (y s) * (π (y s0))⁻¹)
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  have hD : D ≤ δ.ker := by
    rintro x ⟨r, rfl⟩
    change (fun _ : S => π r * (π r)⁻¹) = (1 : S → H)
    funext s
    exact mul_inv_cancel (π r)
  let δbar : B →* (S → H) := QuotientGroup.lift D δ hD
  have hδ : Continuous δ := by
    apply continuous_pi
    intro s
    exact (hπ.comp (continuous_apply s)).mul
      (hπ.comp (continuous_apply s0)).inv
  have hδbar : Continuous δbar := by
    apply (QuotientGroup.isQuotientMap_mk D).continuous_iff.mpr
    change Continuous δ
    exact hδ
  have hpowR (r : R) : π (r ^ n) = 1 :=
    (hker (r ^ n)).mpr ⟨r, rfl⟩
  have hpowB (c : B) : δbar (c ^ n) = 1 := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D c
    change δ (x ^ n) = 1
    funext s
    change π ((x s) ^ n) * (π ((x s0) ^ n))⁻¹ = 1
    rw [hpowR, hpowR]
    exact mul_inv_cancel (1 : H)
  have hroot (b : B) (hb : δbar b = 1) : ∃ c : B, c ^ n = b := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D b
    have hnorm (s : S) : π (x s * (x s0)⁻¹) = 1 := by
      have hs := congrFun hb s
      change π (x s) * (π (x s0))⁻¹ = 1 at hs
      simpa only [map_mul, map_inv] using hs
    choose y hy using fun s => (hker _).mp (hnorm s)
    refine ⟨QuotientGroup.mk' D y, ?_⟩
    change ((y ^ n : S → R) : B) = (x : B)
    apply QuotientGroup.eq_iff_div_mem.mpr
    change ∃ r : R, Pi.constMonoidHom S R r = y ^ n / x
    refine ⟨(x s0)⁻¹, ?_⟩
    funext s
    change (x s0)⁻¹ = y s ^ n / x s
    rw [hy s, div_eq_mul_inv]
    symm
    calc
      (x s * (x s0)⁻¹) * (x s)⁻¹ =
          (x s * (x s)⁻¹) * (x s0)⁻¹ := by ac_rfl
      _ = (x s0)⁻¹ := by rw [mul_inv_cancel, one_mul]
  have hset : {b : B | ∃ c : B, c ^ n = b} =
      δbar ⁻¹' ({1} : Set (S → H)) := by
    ext b
    change (∃ c : B, c ^ n = b) ↔ δbar b = 1
    constructor
    · rintro ⟨c, rfl⟩
      exact hpowB c
    · exact hroot b
  change IsOpen {b : B | ∃ c : B, c ^ n = b}
  rw [hset]
  exact (isOpen_discrete ({1} : Set (S → H))).preimage hδbar

/-- The same nonquadratic coefficient distinguishes any two boundary labels
modulo the diagonal, even when there are exactly two labels. -/
theorem diagonalQuotient_single_injective
    {H S : Type*} [CommGroup H] [DecidableEq S]
    (ζ : H) (hζ : ζ ^ 2 ≠ 1) :
    Function.Injective (fun p : S =>
      (QuotientGroup.mk (fun s : S => if s = p then ζ else 1) :
        (S → H) ⧸ (Pi.constMonoidHom S H).range)) := by
  intro p q hpq
  by_contra hne
  obtain ⟨r, hr⟩ := QuotientGroup.eq_iff_div_mem.mp hpq
  have hp : r = ζ := by
    have h := congrFun hr p
    simpa [hne] using h
  have hq : r = ζ⁻¹ := by
    have h := congrFun hr q
    simpa [Ne.symm hne] using h
  have h := hp.symm.trans hq
  apply hζ
  calc
    ζ ^ 2 = ζ * ζ := pow_two ζ
    _ = ζ * ζ⁻¹ := congrArg (fun a => ζ * a) h
    _ = 1 := mul_inv_cancel ζ

/-- A coefficient homomorphism induces the literal coordinate map modulo
the diagonal relation. -/
def diagonalQuotientMap
    {R H S : Type*} [CommGroup R] [CommGroup H] (π : R →* H) :
    ((S → R) ⧸ (Pi.constMonoidHom S R).range) →*
      ((S → H) ⧸ (Pi.constMonoidHom S H).range) :=
  let f : (S → R) →* (S → H) :=
    { toFun := fun x s => π (x s)
      map_one' := by funext s; exact π.map_one
      map_mul' := by intro x y; funext s; exact π.map_mul (x s) (y s) }
  QuotientGroup.map (Pi.constMonoidHom S R).range (Pi.constMonoidHom S H).range f
    (by rintro x ⟨r, rfl⟩; exact ⟨π r, rfl⟩)

theorem diagonalQuotientMap_single
    {R H S : Type*} [CommGroup R] [CommGroup H] [DecidableEq S]
    (π : R →* H) (p : S) (x : R) :
    diagonalQuotientMap π
        (QuotientGroup.mk (fun s : S => if s = p then x else 1)) =
      QuotientGroup.mk (fun s : S => if s = p then π x else 1) := by
  change QuotientGroup.mk (fun s : S => π (if s = p then x else 1)) = _
  apply congrArg (QuotientGroup.mk : (S → H) →
    ((S → H) ⧸ (Pi.constMonoidHom S H).range))
  funext s
  split_ifs
  · rfl
  · exact π.map_one

theorem diagonalQuotient_pow_eq_one
    {H S : Type*} [CommGroup H] (n : ℕ) (hH : ∀ z : H, z ^ n = 1)
    (b : (S → H) ⧸ (Pi.constMonoidHom S H).range) : b ^ n = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Pi.constMonoidHom S H).range b
  have hx : x ^ n = 1 := by
    funext s
    exact hH (x s)
  rw [← map_pow, hx, map_one]

/-- Equality modulo n-th powers already detects the boundary label when
the coefficient character has exponent n and a nonquadratic value. -/
theorem diagonalQuotient_label_eq_of_div_pow
    {R H S : Type*} [CommGroup R] [CommGroup H] [DecidableEq S]
    (π : R →* H) (n : ℕ) (hH : ∀ z : H, z ^ n = 1)
    (p q : S) (x y : R) (hxy : π x = π y) (hx : (π x) ^ 2 ≠ 1)
    (hpow : ∃ c : (S → R) ⧸ (Pi.constMonoidHom S R).range,
      c ^ n = QuotientGroup.mk (fun s : S => if s = p then x else 1) /
        QuotientGroup.mk (fun s : S => if s = q then y else 1)) :
    p = q := by
  obtain ⟨c, hc⟩ := hpow
  have hm :
      diagonalQuotientMap π
        (QuotientGroup.mk (fun s : S => if s = p then x else 1) /
          QuotientGroup.mk (fun s : S => if s = q then y else 1)) = 1 := by
    rw [← hc, map_pow]
    exact diagonalQuotient_pow_eq_one n hH _
  rw [map_div] at hm
  have heq := div_eq_one.mp hm
  rw [diagonalQuotientMap_single, diagonalQuotientMap_single, ← hxy] at heq
  exact diagonalQuotient_single_injective (π x) hx heq

end AnabelianGeometry.CuspidalInertia
