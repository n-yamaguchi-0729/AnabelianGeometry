/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.FunctionFields.Rational.RatFuncPairSquareMap
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IntermediateField.Basic
import Lean.Elab.Tactic.Omega

/-! # The original quadratic root algebra in the rational root coordinate

A simple pole proves irreducibility of the actual polynomial X squared minus f.
The quotient map sends its actual root to the standard rational coordinate and
its coefficients through the already selected square homomorphism. Its image
contains X and all constants, so it is the entire rational function field.
-/
noncomputable section
open AlgebraicCurve Polynomial
open scoped RatFunc

namespace AnabelianGeometry.KummerTheory

/-- An odd simple pole prevents a root of the quadratic polynomial. -/
theorem squarePolynomial_irreducible_of_simplePole
    {k F : Type} [Field k] [Field F] [Algebra k F]
    (v : Place k F) (f : F) (hv : v.ord f = -1) :
    Irreducible (Polynomial.X ^ 2 - Polynomial.C f) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simpa only [Polynomial.natDegree_X_pow_sub_C, Finset.mem_Icc] using
      (show (1 : ℕ) ≤ 2 ∧ 2 ≤ 3 from by decide)
  · intro z hz
    have hz2 : z ^ 2 = f := by
      simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using hz
    have ho := congrArg v.ord hz2
    rw [← zpow_natCast, v.ord_zpow, hv] at ho
    change (2 : ℤ) * v.ord z = -1 at ho
    omega

/-- The actual quadratic quotient is the literal rational root field. Both its
root and the coefficient map are retained by the same equivalence. -/
theorem ratFuncPairSquare_exists_rootCoordinate
    {k : Type} [Field k] (eF : RatFunc k ≃ₐ[k] RatFunc k)
    (f : RatFunc k) (hf : eF RatFunc.X = f)
    (v : Place k (RatFunc k)) (hv : v.ord f = -1) :
    ∃ e : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C f) ≃ₐ[k] RatFunc k,
      e (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C f)) = RatFunc.X ∧
      ∀ z : RatFunc k,
        e (AdjoinRoot.of (Polynomial.X ^ 2 - Polynomial.C f) z) =
          ratFuncPairSquareHom eF z := by
  let p : (RatFunc k)[X] := Polynomial.X ^ 2 - Polynomial.C f
  let : Fact (Irreducible p) := ⟨squarePolynomial_irreducible_of_simplePole v f hv⟩
  have hroot : p.eval₂ (ratFuncPairSquareHom eF).toRingHom RatFunc.X = 0 := by
    dsimp only [p]
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    change RatFunc.X ^ 2 - ratFuncPairSquareHom eF f = 0
    rw [ratFuncPairSquareHom_apply_pair eF f hf, sub_self]
  let φ : AdjoinRoot p →ₐ[k] RatFunc k :=
    AdjoinRoot.liftAlgHom p (ratFuncPairSquareHom eF) RatFunc.X hroot
  have hφroot : φ (AdjoinRoot.root p) = RatFunc.X :=
    AdjoinRoot.liftAlgHom_root p (ratFuncPairSquareHom eF) RatFunc.X hroot
  have hX : (RatFunc.X : RatFunc k) ∈ φ.fieldRange := ⟨AdjoinRoot.root p, hφroot⟩
  have hpoly : ∀ q : k[X], algebraMap k[X] (RatFunc k) q ∈ φ.fieldRange := by
    intro q
    induction q using Polynomial.induction_on' with
    | add q r hq hr => simpa only [map_add] using φ.fieldRange.add_mem hq hr
    | monomial n c =>
      rw [RatFunc.algebraMap_monomial]
      exact φ.fieldRange.mul_mem (φ.fieldRange.algebraMap_mem c)
        (φ.fieldRange.pow_mem hX n)
  have hsurj : Function.Surjective φ := by
    intro z
    apply (AlgHom.mem_fieldRange (f := φ)).mp
    exact RatFunc.induction_on z
      (fun q r _ => φ.fieldRange.div_mem (hpoly q) (hpoly r))
  refine ⟨AlgEquiv.ofBijective φ ⟨φ.injective, hsurj⟩, hφroot, ?_⟩
  intro z
  exact AdjoinRoot.liftAlgHom_of p (ratFuncPairSquareHom eF) RatFunc.X hroot z

end AnabelianGeometry.KummerTheory
