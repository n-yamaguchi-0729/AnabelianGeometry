/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.OpenCurveCohomologyExactness
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map

/-!
# The residue kernel is proper-curve cohomology

This identifies the kernel by the actual derived compactification pullback,
rather than only by a divisorial model of the proper term.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.WeightFiltration

variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [Algebra.EssFiniteType K F] [IsCurveOver K F]
  (M : CurveModel K F) (n : ℕ+)
  {X : Scheme} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)

/-- Proper finite cohomology identifies with the boundary residue kernel
through the actual compactification pullback, at every geometric base point. -/
def compactificationH1EquivResidueKernel :
    FiniteKummerH1 K M.C n ≃+ (finiteResidue M n j hj hn xi).ker := by
  let f : FiniteKummerH1 K M.C n →+ FiniteKummerH1 K X n :=
    constantCohomologyPullback j
      (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1
  exact
    (AddMonoidHom.ofInjective (f := f)
      (compactificationFiniteH1Pullback_injective M n j xi)).trans
      (AddEquiv.addSubgroupCongr
        (compactificationFiniteH1Pullback_range M n j hj hn xi))

end AnabelianGeometry.WeightFiltration
