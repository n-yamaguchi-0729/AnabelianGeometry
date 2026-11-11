/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Divisors.Modulus.Modulus
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Full modulus congruence in the actual curve stalk

The model's map to its function field constructs the equivalence between the
actual scheme stalk and the valuation ring. This equivalence identifies every
maximal-ideal power, hence also the truncated rings and their unit congruences.
No reduced-support replacement or unspecified local-ring comparison is used.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (x : closedPoints M.C)

/-- The actual stalk maps isomorphically onto the place valuation ring. -/
def stalkValuationEquiv :
    M.C.presheaf.stalk x.1 ≃+* (M.placeOfPoint x).toValuationSubring := by
  let φ : M.C.presheaf.stalk x.1 →+* F :=
    M.ffEquiv.symm.toRingHom.comp (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)
  have hφ : Function.Injective φ :=
    M.ffEquiv.symm.injective.comp
      (IsFractionRing.injective (M.C.presheaf.stalk x.1) M.C.functionField)
  let e : M.C.presheaf.stalk x.1 ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun a b h => hφ (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  exact e.trans (RingEquiv.subringCongr (M.range_stalk_eq x))

/-- The comparison is induced by the specified function-field identification. -/
theorem stalkValuationEquiv_coe (a : M.C.presheaf.stalk x.1) :
    ((M.stalkValuationEquiv x a : (M.placeOfPoint x).toValuationSubring) : F) =
      M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField a) := rfl

/-- The scheme stalk maximal ideal maps to the valuation-ring maximal ideal. -/
theorem stalkValuationEquiv_map_maximalIdeal :
    Ideal.map (M.stalkValuationEquiv x)
        (IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1)) =
      IsLocalRing.maximalIdeal (M.placeOfPoint x).toValuationSubring :=
  IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv (M.stalkValuationEquiv x))

/-- All infinitesimal orders are preserved by the actual local comparison. -/
theorem stalkValuationEquiv_map_maximalIdeal_pow (n : ℕ) :
    Ideal.map (M.stalkValuationEquiv x)
        (IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^ n) =
      IsLocalRing.maximalIdeal (M.placeOfPoint x).toValuationSubring ^ n := by
  rw [Ideal.map_pow, stalkValuationEquiv_map_maximalIdeal]

/-- The actual scheme and valuation truncated local rings agree at every order. -/
def stalkModulusQuotientEquiv (n : ℕ) :
    (M.C.presheaf.stalk x.1 ⧸ IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^ n) ≃+*
      ((M.placeOfPoint x).toValuationSubring ⧸
        IsLocalRing.maximalIdeal (M.placeOfPoint x).toValuationSubring ^ n) :=
  Ideal.quotientEquiv _ _ (M.stalkValuationEquiv x)
    (M.stalkValuationEquiv_map_maximalIdeal_pow x n).symm

/-- The truncated comparison sends the residue of an actual germ to its place residue. -/
theorem stalkModulusQuotientEquiv_mk (n : ℕ) (a : M.C.presheaf.stalk x.1) :
    M.stalkModulusQuotientEquiv x n (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (M.stalkValuationEquiv x a) := rfl

/-- A scheme-stalk unit satisfies exactly the full place congruence of the
same order. The left side is the function-field definition of the modulus. -/
theorem congruentOne_stalkUnit_iff (n : ℕ) (a : (M.C.presheaf.stalk x.1)ˣ) :
    (M.placeOfPoint x).CongruentOne n
        (M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField a)) ↔
      (a : M.C.presheaf.stalk x.1) - 1 ∈
        IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^ n := by
  let e := M.stalkValuationEquiv x
  constructor
  · rintro ⟨b, hb, hmem⟩
    have hba : (b : (M.placeOfPoint x).toValuationSubring) = e a :=
      Subtype.ext (hb.trans (M.stalkValuationEquiv_coe x a).symm)
    have he : e ((a : M.C.presheaf.stalk x.1) - 1) ∈
        Ideal.map e (IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^ n) := by
      rw [map_sub, map_one, M.stalkValuationEquiv_map_maximalIdeal_pow x n, ← hba]
      exact hmem
    exact Ideal.apply_mem_of_equiv_iff.mp he
  · intro hmem
    refine ⟨Units.map e.toMonoidHom a, M.stalkValuationEquiv_coe x a, ?_⟩
    change e (a : M.C.presheaf.stalk x.1) - 1 ∈
      IsLocalRing.maximalIdeal (M.placeOfPoint x).toValuationSubring ^ n
    rw [← map_one e, ← map_sub,
      ← M.stalkValuationEquiv_map_maximalIdeal_pow x n]
    exact Ideal.apply_mem_of_equiv_iff.mpr hmem

/-- Congruence is equivalently equality to one in the actual infinitesimal
neighborhood ring of the point. -/
theorem congruentOne_stalkUnit_iff_quotient_eq_one (n : ℕ)
    (a : (M.C.presheaf.stalk x.1)ˣ) :
    (M.placeOfPoint x).CongruentOne n
        (M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField a)) ↔
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^ n)
        (a : M.C.presheaf.stalk x.1) = 1 := by
  rw [congruentOne_stalkUnit_iff, ← (Ideal.Quotient.mk _).map_one]
  exact Ideal.Quotient.eq.symm

end AlgebraicCurve.CurveModel
