/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Earlier source notices recorded for the cited upstream material:
Copyright (c) 2025 Andrew Yang. All rights reserved.
Authors: Andrew Yang, Kevin Buzzard, Michael Rothgang
https://github.com/ImperialCollegeLondon/FLT/blob/a7dbce8494c29858093974a612a72b6454fc5cba/FLT/Patching/Utils/Depth.lean

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.RingTheory.RegularLocal.ModuleDepthRegularQuotient
public import Nyll.SchemeTheory.RingTheory.Localization.LocalAlgebra

/-!
Module depth is bounded by the dimension of the quotient by an associated prime.
-/

@[expose] public section

open AlgebraicCurves.Foundations.Algebra.Proofs.Module_depth_quotSMulTop_succ_eq

theorem Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    (Module.depth R M : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) :=
  Ws14Port.Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes M hp
