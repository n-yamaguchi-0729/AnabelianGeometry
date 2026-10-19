/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.OpenCurveResidues

/-! # The residue of the original named Kummer class

This computes the actual class, rather than
assuming a comparison with a residue vector. It is the numeric bridge for
the pair-function construction and the named Kummer fiber theorem.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory AlgebraicCurve

namespace AnabelianGeometry.WeightFiltration

variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (n : ℕ+)
  {X : Scheme} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)

/-- The named cover's derived class has exactly the original function orders. -/
theorem finiteResidue_namedKummer_eq_openKummerResidue
    (w : Pic0.openKummerUnits K F (M.openBoundaryPlaces j) n) :
    finiteResidue M n j hj hn xi
      (CurveModel.OpenKummer.kummerEtaleClass M (M.openBoundaryPlaces j) n w j hj
        (M.place_not_mem_openBoundaryPlaces j) hn xi) =
      Multiplicative.toAdd (Pic0.openKummerResidue (M.openBoundaryPlaces j) n w) := by
  have hc : CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn xi
      (Additive.ofMul (QuotientGroup.mk w)) =
    CurveModel.OpenKummer.kummerEtaleClass M (M.openBoundaryPlaces j) n w j hj
      (M.place_not_mem_openBoundaryPlaces j) hn xi := rfl
  rw [← hc, finiteResidue_comparison]
  rfl

/-- Pointwise order formula, with the same function and named class. -/
theorem finiteResidue_namedKummer_apply
    (w : Pic0.openKummerUnits K F (M.openBoundaryPlaces j) n)
    (p : M.openBoundaryPlaces j) :
    finiteResidue M n j hj hn xi
      (CurveModel.OpenKummer.kummerEtaleClass M (M.openBoundaryPlaces j) n w j hj
        (M.place_not_mem_openBoundaryPlaces j) hn xi) p =
      (p.val.ord (w.val : F) : ZMod (n : ℕ)) :=
  congrFun (finiteResidue_namedKummer_eq_openKummerResidue M n j hj hn xi w) p

end AnabelianGeometry.WeightFiltration
