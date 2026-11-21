/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_map_ne_zero_of_tame.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Differentials.Maps.OrdDifferentialMapEq

/-!
# Map ne zero of tame
-/

@[expose] public section

open _root_.AlgebraicCurve in
theorem _root_.AlgebraicCurve.map_ne_zero_of_tame {K : Type*} {F : Type*} {F' : Type*} [Field K]
  [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']
    [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates] [IsCurveOver K F'] [∀ w : Place K F',
      w.DCoordGenerates]
    (hreg : ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)))
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0)
    (w₀ : Place K F') {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    KaehlerDifferential.map K K F F' ω₀ ≠ 0 :=
  AlgebraicCurves.Differentials.Proofs.OrdDifferential_map_eq.AlgebraicCurve.map_ne_zero_of_tame
    (K := K) (F := F) (F' := F') (hreg := hreg) (htame := htame)
    (w₀ := w₀) (ω₀ := ω₀) (hω₀ := hω₀)
