/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitDivisorCoordinates
public import Nyll.AlgebraicCurves.Models.Divisors.CurveNativePicard
public import Nyll.AlgebraicCurves.Models.Kummer.CurveFiniteLevelH2
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Degree
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Every original finite H² class is an actual divisor class

The native Picard comparison and original Kummer boundary show that the
finite divisor-class map is surjective. Its evaluation on the divisor
of an original generic-unit quotient class is the composite of the two
original connecting maps. These representative formulas retain the
original maps needed for arithmetic pullback.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicCurve.CurveModel

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- Every class of the original finite H² is the actual Kummer class
of an original divisor on the curve. -/
theorem nativeFiniteDivisorClass_surjective (n : ℕ) :
    Function.Surjective (M.nativeFiniteDivisorClass ℓ hℓ n) := by
  intro a
  let E := smoothProperCurveFiniteLevelH2EquivH1Quotient K M.toBase ℓ hℓ n
  obtain ⟨b, hb⟩ := Quotient.exists_rep (E a)
  change QuotientAddGroup.mk b = E a at hb
  obtain ⟨D, hD⟩ := Quotient.exists_rep (M.multiplicativeGroupH1PicardEquiv b)
  change H1Gm.mk D = M.multiplicativeGroupH1PicardEquiv b at hD
  refine ⟨D, E.injective ?_⟩
  change E (E.symm (QuotientAddGroup.mk
      (M.multiplicativeGroupH1PicardEquiv.symm (H1Gm.mk D)))) = E a
  rw [E.apply_symm_apply, hD, M.multiplicativeGroupH1PicardEquiv.symm_apply_apply]
  exact hb

/-- The divisor of an original generic-unit quotient class maps to
the composite of the original divisor boundary and Kummer boundary. -/
theorem nativeFiniteDivisorClass_genericUnitBoundary (n : ℕ)
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient M.C) 0) :
    M.nativeFiniteDivisorClass ℓ hℓ n (M.genericUnitDivisorH0Equiv a) =
      (finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 2).symm
        (Sheaf.H.δ (etaleKummerComplex_shortExact M.C
          (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
          (etaleKummerExponentUnit_of_base M.toBase
            (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))) 1 2 rfl
          (Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact M.C) 0 1 rfl a)) := by
  rw [nativeFiniteDivisorClass_boundary,
    multiplicativeGroupH1PicardEquiv_symm_mk, AddEquiv.symm_apply_apply]

/-- The same composite of original boundaries has the degree of its
actual global divisor modulo the original finite exponent. -/
theorem nativeFiniteLevelH2DegreeEquiv_genericUnitBoundary (n : ℕ)
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient M.C) 0) :
    M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
      ((finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 2).symm
        (Sheaf.H.δ (etaleKummerComplex_shortExact M.C
          (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
          (etaleKummerExponentUnit_of_base M.toBase
            (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))) 1 2 rfl
          (Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact M.C) 0 1 rfl a))) =
      (Divisor.degree (M.genericUnitDivisorH0Equiv a) : ZMod (ℓ ^ (n + 1))) := by
  rw [← nativeFiniteDivisorClass_genericUnitBoundary,
    nativeFiniteLevelH2DegreeEquiv_divisor]

end AlgebraicCurve.CurveModel
