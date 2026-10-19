/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationFiniteExtensionValues
import Nyll.AlgebraicCurves.FunctionFields.Constants.RatFuncConstantExtensionPairOrders
import Nyll.AlgebraicCurves.FunctionFields.Rational.RatFuncPairFunctionCoordinate

/-! # The unchanged pair coordinate over the selected finite constant field

The arithmetic pair places are identified from the retained geometric orders,
rather than assumed to match the original labels. The same function then has
its full pair divisor over every separable algebraic constant extension.
Its coordinate over that field is constructed, and if an original coordinate
was already selected, the entire coefficient-extension square commutes.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open AlgebraicGeometry AlgebraicCurve
open scoped Polynomial RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AnabelianGeometry.KummerTheory

private theorem ratFunc_ringHom_eq_of_C_X
    {k L : Type*} [Field k] [Field L] (φ ψ : RatFunc k →+* L)
    (hC : ∀ c : k, φ (RatFunc.C c) = ψ (RatFunc.C c))
    (hX : φ RatFunc.X = ψ RatFunc.X) : φ = ψ := by
  have hpoly (p : Polynomial k) :
      φ (algebraMap (Polynomial k) (RatFunc k) p) =
        ψ (algebraMap (Polynomial k) (RatFunc k) p) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
    | monomial n c =>
      rw [RatFunc.algebraMap_monomial]
      simpa only [map_mul, map_pow] using
        congrArg₂ (· * ·) (hC c) (congrArg (· ^ n) hX)
  apply RingHom.ext
  intro z
  induction z using RatFunc.induction_on with
  | f p q _hq =>
    simpa only [map_div₀] using congrArg₂ (· / ·) (hpoly p) (hpoly q)

/-- Two coordinates for the same function, over the original and extended
constants, intertwine the actual coefficient map on every field element. -/
theorem ratFunc_coordinates_coefficient_commute
    {k E : Type*} [Field k] [Field E] [Algebra k E]
    (e : RatFunc k ≃ₐ[k] RatFunc k) (eE : RatFunc E ≃ₐ[E] RatFunc E)
    (f : RatFunc k) (he : e RatFunc.X = f)
    (heE : eE RatFunc.X = algebraMap (RatFunc k) (RatFunc E) f) :
    ∀ z : RatFunc k,
      eE (algebraMap (RatFunc k) (RatFunc E) z) =
        algebraMap (RatFunc k) (RatFunc E) (e z) := by
  have hcoeff (c : k) :
      algebraMap (RatFunc k) (RatFunc E) (algebraMap k (RatFunc k) c) =
        algebraMap E (RatFunc E) (algebraMap k E c) :=
    (IsScalarTower.algebraMap_apply k (RatFunc k) (RatFunc E) c).symm.trans
      (IsScalarTower.algebraMap_apply k E (RatFunc E) c)
  have hmap := ratFunc_ringHom_eq_of_C_X
    (eE.toRingHom.comp (algebraMap (RatFunc k) (RatFunc E)))
    ((algebraMap (RatFunc k) (RatFunc E)).comp e.toRingHom)
    (fun c => by
      change eE (algebraMap (RatFunc k) (RatFunc E) (RatFunc.C c)) =
        algebraMap (RatFunc k) (RatFunc E) (e (RatFunc.C c))
      rw [← RatFunc.algebraMap_eq_C, e.commutes, hcoeff, eE.commutes])
    (by
      change eE (algebraMap (RatFunc k) (RatFunc E) RatFunc.X) =
        algebraMap (RatFunc k) (RatFunc E) (e RatFunc.X)
      rw [ratFunc_constantExtension_map_X, heE, he])
  exact DFunLike.congr_fun hmap

end AnabelianGeometry.KummerTheory

namespace AlgebraicGeometry.ProjSpace

open AnabelianGeometry.KummerTheory

/-- The original labels determine both retained arithmetic pair-place
witnesses, using only the two complete order formulas for the same f. -/
theorem rationalConfiguration_pairFunction_arithmeticPlaces_eq_literal
    (k κ : Type) [Field k] [Field κ] [Algebra k κ]
    [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]
    (s : Finset (Projectivization k (k × k))) (a b : s) (hab : a ≠ b)
    (V₀ Vinf : Place k (RatFunc k)) (f : RatFunc k)
    (harith : ∀ V : Place k (RatFunc k),
      V.ord f = (if V = V₀ then 1 else 0) - (if V = Vinf then 1 else 0))
    (hgeom : ∀ W : Place κ (RatFunc κ),
      W.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
        (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
        (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0)) :
    V₀ = literalRationalPuncturePlace k a.val.rep a.val.rep_nonzero ∧
      Vinf = literalRationalPuncturePlace k b.val.rep b.val.rep_nonzero := by
  have hWab : (rationalConfigurationBoundaryPlace k κ s a).val ≠
      (rationalConfigurationBoundaryPlace k κ s b).val := by
    intro h
    exact hab ((rationalConfigurationBoundaryPlaceEquiv k κ s).injective (Subtype.ext h))
  have ha : (literalRationalPuncturePlace k a.val.rep a.val.rep_nonzero).ord f = 1 := by
    rw [← rationalConfigurationBoundaryPlace_coefficient_orders k κ s a f,
      hgeom, ite_eq_left rfl, ite_eq_right hWab, sub_zero]
  have hb : (literalRationalPuncturePlace k b.val.rep b.val.rep_nonzero).ord f = -1 := by
    rw [← rationalConfigurationBoundaryPlace_coefficient_orders k κ s b f,
      hgeom, ite_eq_right hWab.symm, ite_eq_left rfl, zero_sub]
  constructor
  · symm
    by_contra h
    have h' := harith (literalRationalPuncturePlace k a.val.rep a.val.rep_nonzero)
    rw [ha, ite_eq_right h] at h'
    split_ifs at h' <;> norm_num at h'
  · symm
    by_contra h
    have h' := harith (literalRationalPuncturePlace k b.val.rep b.val.rep_nonzero)
    rw [hb, ite_eq_right h] at h'
    split_ifs at h' <;> norm_num at h'

/-- The same f has its full pair divisor at the original finite-extension
labels, and supplies a coordinate over E. Every required rationality and
place-distinctness assertion is proved from the actual labels. -/
theorem rationalConfiguration_pairFunction_finiteExtension_orders_coordinate
    (k κ E : Type) [Field k] [Field κ] [Field E]
    [Algebra k κ] [Algebra k E]
    [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]
    [Algebra.IsAlgebraic k E] [Algebra.IsSeparable k E]
    (s : Finset (Projectivization k (k × k))) (a b : s) (hab : a ≠ b)
    (V₀ Vinf : Place k (RatFunc k)) (f : RatFunc k)
    (harith : ∀ V : Place k (RatFunc k),
      V.ord f = (if V = V₀ then 1 else 0) - (if V = Vinf then 1 else 0))
    (hgeom : ∀ W : Place κ (RatFunc κ),
      W.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
        (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
        (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0)) :
    (∀ W : Place E (RatFunc E),
      W.ord (algebraMap (RatFunc k) (RatFunc E) f) =
        (if W = (rationalConfigurationBoundaryPlace k E s a).val then 1 else 0) -
        (if W = (rationalConfigurationBoundaryPlace k E s b).val then 1 else 0)) ∧
    ∃ eE : RatFunc E ≃ₐ[E] RatFunc E,
      eE RatFunc.X = algebraMap (RatFunc k) (RatFunc E) f := by
  obtain ⟨h₀, hinf⟩ := rationalConfiguration_pairFunction_arithmeticPlaces_eq_literal
    k κ s a b hab V₀ Vinf f harith hgeom
  have hliteral : ∀ V : Place k (RatFunc k),
      V.ord f =
        (if V = literalRationalPuncturePlace k a.val.rep a.val.rep_nonzero then 1 else 0) -
        (if V = literalRationalPuncturePlace k b.val.rep b.val.rep_nonzero then 1 else 0) := by
    intro V
    simpa only [h₀, hinf] using harith V
  have horders := ratFunc_constantExtension_pair_orders
    (literalRationalPuncturePlace k a.val.rep a.val.rep_nonzero)
    (literalRationalPuncturePlace k b.val.rep b.val.rep_nonzero)
    (literalRationalPuncturePlace_isRational k _ _)
    (literalRationalPuncturePlace_isRational k _ _)
    (rationalConfigurationBoundaryPlace k E s a).val
    (rationalConfigurationBoundaryPlace k E s b).val
    (rationalConfigurationBoundaryPlace_coefficient_orders k E s a)
    (rationalConfigurationBoundaryPlace_coefficient_orders k E s b) f hliteral
  have hWinf : (rationalConfigurationBoundaryPlace k E s b).val.IsRational := by
    change (literalRationalPuncturePlace E (extendedPunctureCoordinates k E b.val)
      (extendedPunctureCoordinates_ne_zero k E b.val)).IsRational
    exact literalRationalPuncturePlace_isRational E _ _
  have hWdistinct : (rationalConfigurationBoundaryPlace k E s a).val ≠
      (rationalConfigurationBoundaryPlace k E s b).val := by
    intro h
    exact hab ((rationalConfigurationBoundaryPlaceEquiv k E s).injective (Subtype.ext h))
  exact ⟨horders, ratFunc_exists_algEquiv_apply_X_of_pair_orders
    (rationalConfigurationBoundaryPlace k E s a).val
    (rationalConfigurationBoundaryPlace k E s b).val hWinf hWdistinct
    (algebraMap (RatFunc k) (RatFunc E) f) horders⟩

/-- Retain an already selected original coordinate and construct a compatible
E-coordinate of the same f; the coefficient square commutes on the full field. -/
theorem rationalConfiguration_pairFunction_finiteExtension_coordinate_commutes
    (k κ E : Type) [Field k] [Field κ] [Field E]
    [Algebra k κ] [Algebra k E]
    [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]
    [Algebra.IsAlgebraic k E] [Algebra.IsSeparable k E]
    (s : Finset (Projectivization k (k × k))) (a b : s) (hab : a ≠ b)
    (V₀ Vinf : Place k (RatFunc k)) (f : RatFunc k)
    (harith : ∀ V : Place k (RatFunc k),
      V.ord f = (if V = V₀ then 1 else 0) - (if V = Vinf then 1 else 0))
    (hgeom : ∀ W : Place κ (RatFunc κ),
      W.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
        (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
        (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0))
    (e : RatFunc k ≃ₐ[k] RatFunc k) (he : e RatFunc.X = f) :
    ∃ eE : RatFunc E ≃ₐ[E] RatFunc E,
      eE RatFunc.X = algebraMap (RatFunc k) (RatFunc E) f ∧
      ∀ z : RatFunc k,
        eE (algebraMap (RatFunc k) (RatFunc E) z) =
          algebraMap (RatFunc k) (RatFunc E) (e z) := by
  obtain ⟨_, eE, heE⟩ := rationalConfiguration_pairFunction_finiteExtension_orders_coordinate
    k κ E s a b hab V₀ Vinf f harith hgeom
  exact ⟨eE, heE, ratFunc_coordinates_coefficient_commute e eE f he heE⟩

end AlgebraicGeometry.ProjSpace
