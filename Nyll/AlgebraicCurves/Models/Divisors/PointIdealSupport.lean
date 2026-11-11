/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # The support of the actual ideal of a closed point -/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)

/-- The kernel ideal of the actual rational point has exactly its closed support. -/
theorem pointOfClosedPoint_ker_support (x : closedPoints M.C) :
    ((pointOfClosedPoint M.toBase x.1 x.2).ker.support : Set M.C) = {x.1} := by
  let p := pointOfClosedPoint M.toBase x.1 x.2
  have : IsClosedImmersion p :=
    isClosedImmersion_of_comp_eq_id M.toBase p (pointOfClosedPoint_comp M.toBase x.1 x.2)
  change (p.ker.support : Set M.C) = {x.1}
  rw [Scheme.Hom.support_ker, p.isClosedEmbedding.isClosed_range.closure_eq]
  exact Set.range_eq_singleton (fun y => pointOfClosedPoint_apply M.toBase x.1 x.2 y)

end AlgebraicCurve.CurveModel
