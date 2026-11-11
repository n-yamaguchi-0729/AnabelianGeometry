/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Divisors.SubschemeStalk
public import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # The full stalk ideal of a rational closed point -/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The defining ideal of an actual rational closed immersion is the maximal
ideal of the ambient stalk at its point. -/
theorem Hom.ker_stalkIdeal_closedPoint {K : Type u} [Field K] {X : Scheme.{u}}
    (p : Spec (CommRingCat.of K) ⟶ X) [IsClosedImmersion p] :
    p.ker.stalkIdeal (p (IsLocalRing.closedPoint K)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (p (IsLocalRing.closedPoint K))) := by
  let e := stalkClosedPointIso (CommRingCat.of K)
  have hsurj : Function.Surjective (stalkClosedPointTo p).hom :=
    e.commRingCatIsoToRingEquiv.surjective.comp
      (p.stalkMap_surjective (IsLocalRing.closedPoint K))
  calc
    p.ker.stalkIdeal (p (IsLocalRing.closedPoint K)) =
        RingHom.ker (p.stalkMap (IsLocalRing.closedPoint K)).hom :=
      (p.ker_stalkMap_eq_stalkIdeal (IsLocalRing.closedPoint K)).symm
    _ = RingHom.ker (stalkClosedPointTo p).hom :=
      (RingHom.ker_comp_of_injective (p.stalkMap (IsLocalRing.closedPoint K)).hom
        e.commRingCatIsoToRingEquiv.injective).symm
    _ = IsLocalRing.maximalIdeal _ := IsLocalRing.ker_eq_maximalIdeal _ hsurj

namespace IdealSheafData

/-- Powers retain their exact exponent under passage to actual stalk ideals. -/
theorem stalkIdeal_pow {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) (x : X) :
    (I ^ n).stalkIdeal x = I.stalkIdeal x ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, one_eq_top, stalkIdeal_top, Ideal.one_eq_top]
  | succ n ih => rw [pow_succ, pow_succ, stalkIdeal_mul, ih]

end IdealSheafData
end AlgebraicGeometry.Scheme
