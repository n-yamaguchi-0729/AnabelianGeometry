/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Differentials.Local.Order
import Nyll.AlgebraicCurves.Differentials.Local.Uniformizer
import Nyll.AlgebraicCurves.Differentials.Local.LocalGeometry

/-!
# Local Unit Derivative Regular of is Curve Over
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.LocalUnitDerivativeRegularCurve
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

theorem differentialCoeff_D_unit_eq_zero_or_ord_nonneg {K : Type*} {F' : Type*} [Field K] [Field
  F'] [Algebra K F']
    [PerfectField K] [Algebra.EssFiniteType K F'] [IsCurveOver K F'] [∀ w : Place K F',
      w.DCoordGenerates] :
    ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)) := by
  intro w u hu h0
  have : Nontrivial Ω[F'⁄K] :=
    Module.nontrivial_of_finrank_eq_succ (IsCurveOver.kaehler_free_rank_one (K := K) (F := F')).2
  have hu_mem : u ∈ w.toValuationSubring := w.mem_of_ord_nonneg hu (by rw [h0])
  obtain ⟨c, hc, hcu⟩ :=
    exists_mem_D_eq_smul_D_of_isCurveOver (K := K) w (π := w.uniformizer) w.ord_uniformizer hu_mem
  have hcoeff : w.differentialCoeff (KaehlerDifferential.D K F' u) = c :=
    w.differentialCoeff_unique (by rw [hcu]; rfl)
  rw [hcoeff]
  rcases eq_or_ne c 0 with rfl | hc0
  · exact Or.inl rfl
  · exact Or.inr (w.ord_nonneg_of_mem hc)
end AlgebraicCurve

open _root_.AlgebraicCurve
  _root_.AlgebraicCurves.Differentials.Proofs.LocalUnitDerivativeRegularCurve.AlgebraicCurve in
theorem _root_.AlgebraicCurve.localUnitDerivativeRegular_of_isCurveOver {K : Type*} {F' : Type*}
  [Field K] [Field F'] [Algebra K F']
    [PerfectField K] [Algebra.EssFiniteType K F'] [IsCurveOver K F'] [∀ w : Place K F',
      w.DCoordGenerates] :
    ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)) :=
  AlgebraicCurve.differentialCoeff_D_unit_eq_zero_or_ord_nonneg
end AlgebraicCurves.Differentials.Proofs.LocalUnitDerivativeRegularCurve
end ProofImplementation
