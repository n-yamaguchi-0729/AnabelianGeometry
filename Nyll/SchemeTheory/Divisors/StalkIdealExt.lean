/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale

/-!
# Ideal sheaves are determined by their actual stalk ideals

Containment and equality of ideal sheaves can be checked at every stalk.
This follows from affine ideal detection and the proved affine-neighborhood
description of the actual stalk ideal, without a coherence hypothesis.
-/

@[expose] public section

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {I J : X.IdealSheafData}

/-- Containment of actual ideal sheaves is detected by all stalk ideals. -/
theorem le_iff_stalkIdeal_le : I ≤ J ↔ ∀ x : X, I.stalkIdeal x ≤ J.stalkIdeal x := by
  refine ⟨fun h x => stalkIdeal_mono h x, ?_⟩
  intro h U
  apply U.2.ideal_le_iff.mpr
  intro x hx
  rw [← I.stalkIdeal_eq_map_ideal x U hx, ← J.stalkIdeal_eq_map_ideal x U hx]
  exact h x

/-- Equality of the complete local ideals implies equality of the ideal
sheaves, retaining all nilpotent thicknesses. -/
theorem ext_of_stalkIdeal_eq (h : ∀ x : X, I.stalkIdeal x = J.stalkIdeal x) : I = J :=
  le_antisymm (le_iff_stalkIdeal_le.mpr (fun x => (h x).le))
    (le_iff_stalkIdeal_le.mpr (fun x => (h x).ge))

/-- Equality of ideal sheaves is equivalent to equality at every stalk. -/
theorem eq_iff_stalkIdeal_eq : I = J ↔ ∀ x : X, I.stalkIdeal x = J.stalkIdeal x :=
  ⟨fun h x => congrArg (fun L : X.IdealSheafData => L.stalkIdeal x) h,
    ext_of_stalkIdeal_eq⟩

end AlgebraicGeometry.Scheme.IdealSheafData
