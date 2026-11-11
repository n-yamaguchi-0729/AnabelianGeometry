/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitDivisorCoordinates
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.GenericUnitOpenCohomology
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Frobenius.KummerCoefficients
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Boundary
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Degree
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Inverse arithmetic action on the original finite divisor classes

The actual coefficient twist and naturality of the two original
connecting maps compute the action on divisor classes. Only the
geometric semilinearity equation for the given scheme isomorphism is
used; no cohomological equivariance is supplied as an assumption.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicCurve.CurveModel

variable (k K : Type u) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  {F : Type u} [Field F] [Algebra K F]
  (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The original inverse-arithmetic pullback of a finite divisor class
is cardinality times the class of the actually pulled divisor. -/
theorem nativeFiniteDivisorClass_inverseArithmetic
    (e : M.C ≅ M.C)
    (he : e.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm.toRingHom))
    (n : ℕ) (a : Sheaf.H.{u} (etaleGenericUnitQuotient M.C) 0) :
    finiteLevelCohomologyPullback ℓ e.hom n 2
        (M.nativeFiniteDivisorClass ℓ hℓ n (M.genericUnitDivisorH0Equiv a)) =
      (Fintype.card k) • M.nativeFiniteDivisorClass ℓ hℓ n
        (M.genericUnitDivisorH0Equiv
          (etaleGenericUnitQuotientCohomologyPullback e.hom 0 a)) := by
  apply (finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 2).injective
  rw [finiteLevelKummerCohomologyEquiv_inverseArithmetic k K M.toBase ℓ hℓ
    e.hom he, map_nsmul]
  simp only [nativeFiniteDivisorClass_genericUnitBoundary, AddEquiv.apply_symm_apply]
  have hn : 0 < ℓ ^ (n + 1) := pow_pos (Fact.out : ℓ.Prime).pos (n + 1)
  have hnM : IsUnit ((ℓ ^ (n + 1) : ℕ) : Γ(M.C, ⊤)) :=
    etaleKummerExponentUnit_of_base M.toBase
      (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1))
  have hgeneric := etaleGenericUnitBoundary_zero_pullback e.hom a
  have hkummer := etaleKummerBoundary_one_pullback e.hom hn hnM
    (Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact M.C) 0 1 rfl a)
  have hboundary := congrArg
    (fun z : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf M.C) 1 =>
      Sheaf.H.δ (etaleKummerComplex_shortExact M.C hn hnM) 1 2 rfl z) hgeneric
  exact congrArg
    (fun z : Sheaf.H.{u} (etaleRootsOfUnitySheaf M.C (ℓ ^ (n + 1))) 2 =>
      (Fintype.card k) • z) (hkummer.trans hboundary)

end AlgebraicCurve.CurveModel
