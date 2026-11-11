/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Divisors.CartierStalkMultiplicity
public import Nyll.AlgebraicCurves.Models.Charts.FiniteComplIsOpen
public import Nyll.SchemeTheory.Divisors.StalkIdealSupport

/-!
# The function-field modulus of an actual Cartier divisor

The exponent at each place is constructed from the actual defining stalk ideal.
It vanishes exactly outside the Cartier support, which is finite on a proper
curve. Thus the scheme modulus supplies an actual finitely supported
function-field modulus with its complete multiplicities.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (I : M.C.IdealSheafData) (hI : I.IsInvertible)

/-- The exponent is zero exactly away from the scheme-theoretic Cartier support. -/
theorem cartierMultiplicity_eq_zero_iff (x : closedPoints M.C) :
    M.cartierMultiplicity I hI x = 0 ↔ x.1 ∉ I.support := by
  have h : I.stalkIdeal x.1 = ⊤ ↔ M.cartierMultiplicity I hI x = 0 := by
    rw [M.stalkIdeal_eq_maximalIdeal_pow I hI x, Ideal.pow_eq_top_iff]
    exact or_iff_right (IsLocalRing.maximalIdeal.isMaximal (M.C.presheaf.stalk x.1)).ne_top
  exact h.symm.trans (I.stalkIdeal_eq_top_iff_notMem_support x.1)

include hI in
/-- A Cartier ideal on the model has finite support, proved from the nonzero
generic stalk and the one-dimensional geometry of the curve. -/
theorem cartierSupport_finite : (I.support : Set M.C).Finite := by
  have htop : I.stalkIdeal (genericPoint M.C) = ⊤ := by
    let J : Ideal M.C.functionField := I.stalkIdeal (genericPoint M.C)
    exact (Ideal.eq_bot_or_top J).resolve_left (hI.stalkIdeal_ne_bot (genericPoint M.C))
  have hη : genericPoint M.C ∉ I.support :=
    (I.stalkIdeal_eq_top_iff_notMem_support (genericPoint M.C)).mp htop
  have h := finite_compl_of_isOpen M.toBase I.support.compl ⟨genericPoint M.C, hη⟩
  simpa only [TopologicalSpace.Closeds.coe_compl, compl_compl] using h

/-- The actual multiplicity function is finitely supported. -/
theorem cartierMultiplicity_support_finite :
    (Function.support (fun w : Place K F =>
      M.cartierMultiplicity I hI (M.placeEquiv.symm w))).Finite := by
  let p : Place K F → M.C := fun w => (M.placeEquiv.symm w).1
  have hp : Function.Injective p := Subtype.val_injective.comp M.placeEquiv.symm.injective
  have hpre : (p ⁻¹' (I.support : Set M.C)).Finite :=
    Set.Finite.preimage hp.injOn (M.cartierSupport_finite I hI)
  apply hpre.subset
  intro w hw
  change M.cartierMultiplicity I hI (M.placeEquiv.symm w) ≠ 0 at hw
  change (M.placeEquiv.symm w).1 ∈ I.support
  by_contra hn
  exact hw ((M.cartierMultiplicity_eq_zero_iff I hI (M.placeEquiv.symm w)).mpr hn)

/-- The full function-field modulus associated to the actual Cartier ideal. -/
def cartierModulus : Modulus K F :=
  Finsupp.ofSupportFinite
    (fun w => M.cartierMultiplicity I hI (M.placeEquiv.symm w))
    (M.cartierMultiplicity_support_finite I hI)

/-- The modulus coefficient is the order of the actual stalk ideal. -/
theorem cartierModulus_apply (w : Place K F) :
    M.cartierModulus I hI w = M.cartierMultiplicity I hI (M.placeEquiv.symm w) := rfl

/-- Its support condition agrees with support of the original scheme modulus. -/
theorem cartierModulus_eq_zero_iff (w : Place K F) :
    M.cartierModulus I hI w = 0 ↔ (M.placeEquiv.symm w).1 ∉ I.support :=
  M.cartierMultiplicity_eq_zero_iff I hI (M.placeEquiv.symm w)

end AlgebraicCurve.CurveModel
