/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained below.
-/

module

public import Mathlib.RingTheory.Valuation.RamificationGroup


/-! # Valuation inertia as a subgroup of field automorphisms

The elliptic-curve and Frey-package definitions in the upstream source are not needed here.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (valuation-inertia definition only):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_FLTPrelim_Ramification.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/




namespace ValuationSubring

variable {L : Type*} [Field L] (K : Type*) [Field K] [Algebra K L]

/-- The image of valuation inertia in the automorphism group of the ambient field. -/
noncomputable def inertiaSubgroupIn (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype

end ValuationSubring

end
