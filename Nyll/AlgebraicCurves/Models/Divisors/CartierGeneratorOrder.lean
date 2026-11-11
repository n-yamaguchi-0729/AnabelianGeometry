/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The valuation-ring argument below is adapted from the private lemma in
Nyll/AlgebraicCurves/Places/Place_ord_norm_eq_sum_fiberOver.lean.
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

module

public import Nyll.AlgebraicCurves.Models.Divisors.CartierStalkMultiplicity
public import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Local generator orders are the constructed Cartier multiplicities

The rational function of any actual local ideal generator has valuation equal
to the complete Cartier multiplicity. This supplies the coefficient comparison
between section ratios and differences of effective Cartier divisors.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry

namespace AlgebraicCurve

/-- A principal ideal equal to the `n`-th maximal-ideal power has generator
order exactly `n`, with no chosen-generator normalization hypothesis. -/
theorem Place.ord_coe_of_span_eq_maximalIdeal_pow
    {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
    {r : w.toValuationSubring} {n : ℕ}
    (h : Ideal.span {r} = IsLocalRing.maximalIdeal w.toValuationSubring ^ n) :
    w.ord (r : F) = n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
  obtain ⟨a, ha⟩ := h
  have hr : r = ((a⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) * π ^ n := by
    rw [mul_comm, Units.eq_mul_inv_iff_mul_eq]
    exact ha
  have hcoe : (r : F) = (((a⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) : F)
      * (π : F) ^ (n : ℤ) := by
    rw [hr]
    push_cast
    rw [zpow_natCast]
  rw [hcoe, w.ord_unit_smul_zpow a⁻¹ hπ (n : ℤ)]

namespace CurveModel

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (I : M.C.IdealSheafData) (hI : I.IsInvertible)

/-- A generator of the actual ideal in the curve stalk has exactly its
constructed Cartier multiplicity under the specified function-field map. -/
theorem ord_stalkGenerator (x : closedPoints M.C) (a : M.C.presheaf.stalk x.1)
    (ha : I.stalkIdeal x.1 = Ideal.span {a}) :
    (M.placeOfPoint x).ord
        (M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField a)) =
      M.cartierMultiplicity I hI x := by
  have he := congrArg (Ideal.map (M.stalkValuationEquiv x))
    (ha.symm.trans (M.stalkIdeal_eq_maximalIdeal_pow I hI x))
  rw [Ideal.map_span, Set.image_singleton,
    M.stalkValuationEquiv_map_maximalIdeal_pow x] at he
  have ho := (M.placeOfPoint x).ord_coe_of_span_eq_maximalIdeal_pow he
  rw [M.stalkValuationEquiv_coe] at ho
  exact ho

/-- A regular affine local equation of the Cartier ideal has the same exact
order as the constructed multiplicity at every point of that chart. -/
theorem ord_affineGenerator (U : M.C.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (g : Γ(M.C, U)) (hg : I.ideal ⟨U, hU⟩ = Ideal.span {g})
    (x : closedPoints M.C) (hx : x.1 ∈ U) :
    (M.placeOfPoint x).ord (M.ffEquiv.symm (M.C.germToFunctionField U g)) =
      M.cartierMultiplicity I hI x := by
  have hs : I.stalkIdeal x.1 = Ideal.span {(M.C.presheaf.germ U x.1 hx).hom g} := by
    rw [I.stalkIdeal_eq_map_ideal x.1 ⟨U, hU⟩ hx, hg,
      Ideal.map_span, Set.image_singleton]
  have h := M.ord_stalkGenerator I hI x ((M.C.presheaf.germ U x.1 hx).hom g) hs
  rw [M.C.algebraMap_germ_eq_germToFunctionField hx] at h
  exact h

include hI in
/-- An actual Cartier stalk generator gives a nonzero rational function. -/
theorem stalkGenerator_function_ne_zero (x : closedPoints M.C)
    (a : M.C.presheaf.stalk x.1) (ha : I.stalkIdeal x.1 = Ideal.span {a}) :
    M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField a) ≠ 0 := by
  intro hz
  have hzero : a = 0 :=
    (IsFractionRing.injective (M.C.presheaf.stalk x.1) M.C.functionField)
      ((M.ffEquiv.symm.injective (hz.trans (map_zero M.ffEquiv.symm).symm)).trans
        (map_zero (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)).symm)
  apply hI.stalkIdeal_ne_bot x.1
  rw [ha, hzero, Ideal.span_singleton_zero]

/-- The ratio of actual Cartier stalk generators has the difference of the
constructed multiplicities. This is the local principal-divisor formula. -/
theorem ord_stalkGenerator_ratio (J : M.C.IdealSheafData) (hJ : J.IsInvertible)
    (x : closedPoints M.C) (a b : M.C.presheaf.stalk x.1)
    (ha : I.stalkIdeal x.1 = Ideal.span {a})
    (hb : J.stalkIdeal x.1 = Ideal.span {b}) :
    (M.placeOfPoint x).ord
        (M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField a) /
          M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField b)) =
      (M.cartierMultiplicity I hI x : ℤ) - (M.cartierMultiplicity J hJ x : ℤ) := by
  rw [div_eq_mul_inv,
    (M.placeOfPoint x).ord_mul (M.stalkGenerator_function_ne_zero I hI x a ha)
      (inv_ne_zero (M.stalkGenerator_function_ne_zero J hJ x b hb)),
    Place.ord_inv, M.ord_stalkGenerator I hI x a ha,
    M.ord_stalkGenerator J hJ x b hb, sub_eq_add_neg]

end CurveModel
end AlgebraicCurve
