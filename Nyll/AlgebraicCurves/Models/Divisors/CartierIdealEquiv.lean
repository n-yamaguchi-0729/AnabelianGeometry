/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Divisors.CartierPointDecomposition
public import Nyll.SchemeTheory.Divisors.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.HomInvertibleKerCompEqId
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealPow

/-!
# Effective Cartier ideals and nonnegative place divisors

The exact point-ideal decomposition gives both directions of the
correspondence. Uniqueness of powers in the actual discrete valuation rings
also proves additivity of the constructed multiplicity under ideal products.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F)

/-- Distinct natural exponents give distinct maximal-ideal powers in a curve stalk. -/
theorem stalk_maximalIdeal_pow_injective (x : closedPoints M.C) :
    Function.Injective (fun n : ℕ =>
      IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^ n) := by
  intro m n h
  have he := congrArg (Ideal.map (M.stalkValuationEquiv x)) h
  rw [M.stalkValuationEquiv_map_maximalIdeal_pow x m,
    M.stalkValuationEquiv_map_maximalIdeal_pow x n] at he
  have hc := congrArg Order.coheight he
  rw [IsDiscreteValuationRing.coheight_pow_maximalIdeal,
    IsDiscreteValuationRing.coheight_pow_maximalIdeal] at hc
  exact ENat.natCast_inj.mp hc

/-- Exact multiplicities add under multiplication of actual Cartier ideals. -/
theorem cartierMultiplicity_mul (I J : M.C.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (x : closedPoints M.C) :
    M.cartierMultiplicity (I * J) (hI.mul hJ) x =
      M.cartierMultiplicity I hI x + M.cartierMultiplicity J hJ x := by
  apply M.stalk_maximalIdeal_pow_injective x
  change IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^
      M.cartierMultiplicity (I * J) (hI.mul hJ) x =
    IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^
      (M.cartierMultiplicity I hI x + M.cartierMultiplicity J hJ x)
  rw [← M.stalkIdeal_eq_maximalIdeal_pow (I * J) (hI.mul hJ) x,
    Scheme.IdealSheafData.stalkIdeal_mul, M.stalkIdeal_eq_maximalIdeal_pow I hI x,
    M.stalkIdeal_eq_maximalIdeal_pow J hJ x, pow_add]

/-- The constructed function-field modulus converts ideal multiplication to addition. -/
theorem cartierModulus_mul (I J : M.C.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    M.cartierModulus (I * J) (hI.mul hJ) = M.cartierModulus I hI + M.cartierModulus J hJ := by
  ext w
  exact M.cartierMultiplicity_mul I J hI hJ (M.placeEquiv.symm w)

/-- Inclusion of actual Cartier ideals reverses the order of their full stalk
multiplicities, since distinct maximal-ideal powers have distinct exponents. -/
theorem cartierMultiplicity_antitone {I J : M.C.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (hIJ : I ≤ J)
    (x : closedPoints M.C) :
    M.cartierMultiplicity J hJ x ≤ M.cartierMultiplicity I hI x := by
  by_contra hn
  have hrev : M.cartierMultiplicity I hI x ≤ M.cartierMultiplicity J hJ x :=
    (Nat.lt_of_not_ge hn).le
  have hstalk := Scheme.IdealSheafData.stalkIdeal_mono hIJ x.1
  rw [M.stalkIdeal_eq_maximalIdeal_pow I hI x,
    M.stalkIdeal_eq_maximalIdeal_pow J hJ x] at hstalk
  have he := M.stalk_maximalIdeal_pow_injective x
    (le_antisymm hstalk (Ideal.pow_le_pow_right hrev))
  exact hn (Nat.le_of_eq he.symm)

/-- A thicker scheme-theoretic modulus gives a larger function-field modulus,
with every multiplicity retained. -/
theorem cartierModulus_antitone {I J : M.C.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (hIJ : I ≤ J) :
    M.cartierModulus J hJ ≤ M.cartierModulus I hI :=
  fun w => M.cartierMultiplicity_antitone hI hJ hIJ (M.placeEquiv.symm w)

variable [IsAlgClosed K]

/-- Every finite point-ideal product is an actual effective Cartier ideal. -/
theorem pointIdealProduct_isInvertible (D : Modulus K F) :
    (M.pointIdealProduct D).IsInvertible := by
  classical
  unfold pointIdealProduct
  have hp : ∀ w : Place K F,
      ((pointOfClosedPoint M.toBase (M.placeEquiv.symm w).1
        (M.placeEquiv.symm w).2).ker ^ D w).IsInvertible := by
    intro w
    exact (Scheme.Hom.isInvertible_ker_of_comp_eq_id _
      (pointOfClosedPoint_comp M.toBase (M.placeEquiv.symm w).1
        (M.placeEquiv.symm w).2)).pow (D w)
  induction D.support using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact Scheme.IdealSheafData.isInvertible_top
  | @insert w s hw ih =>
    rw [Finset.prod_insert hw]
    exact (hp w).mul ih

/-- The actual point-ideal product recovers precisely the specified coefficients. -/
theorem cartierModulus_pointIdealProduct (D : Modulus K F) :
    M.cartierModulus (M.pointIdealProduct D) (M.pointIdealProduct_isInvertible D) = D := by
  ext w
  let x := M.placeEquiv.symm w
  change M.cartierMultiplicity (M.pointIdealProduct D)
    (M.pointIdealProduct_isInvertible D) x = D w
  apply M.stalk_maximalIdeal_pow_injective x
  change IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^
      M.cartierMultiplicity (M.pointIdealProduct D) (M.pointIdealProduct_isInvertible D) x =
    IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^ D w
  rw [← M.stalkIdeal_eq_maximalIdeal_pow (M.pointIdealProduct D)
    (M.pointIdealProduct_isInvertible D) x, M.pointIdealProduct_stalkIdeal D x]
  change IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^
      D (M.placeEquiv (M.placeEquiv.symm w)) = _
  rw [M.placeEquiv.apply_symm_apply]

/-- Actual effective Cartier ideals correspond to nonnegative place divisors,
with inverse given by the proved finite product of actual point kernels. -/
def cartierIdealEquiv : {I : M.C.IdealSheafData // I.IsInvertible} ≃ Modulus K F where
  toFun I := M.cartierModulus I.1 I.2
  invFun D := ⟨M.pointIdealProduct D, M.pointIdealProduct_isInvertible D⟩
  left_inv I := Subtype.ext (M.eq_pointIdealProduct_cartierModulus I.1 I.2).symm
  right_inv := M.cartierModulus_pointIdealProduct

end AlgebraicCurve.CurveModel
