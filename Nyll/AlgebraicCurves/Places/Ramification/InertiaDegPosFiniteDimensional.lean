/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


import Nyll.AlgebraicCurves.Places.Residue.FiniteResidueFieldFiniteDimensional

/-!
# Positivity of the residue degree of a finite extension
-/

theorem _root_.AlgebraicCurve.Place.inertiaDeg_pos_of_finiteDimensional {K F F' : Type*} [Field K]
  [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] (w : AlgebraicCurve.Place K F') : 0 < w.inertiaDeg F := by
  have : Module.Finite (w.restrict F).ResidueField w.ResidueField :=
    AlgebraicCurve.Place.finite_residueField_of_finiteDimensional (F := F) w
  exact Module.finrank_pos
