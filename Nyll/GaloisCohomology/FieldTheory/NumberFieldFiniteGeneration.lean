/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.FieldTheory.FinitelyGeneratedExtensions
public import Mathlib.NumberTheory.NumberField.Basic

/-! # Number fields are finitely generated fields -/

@[expose] public section

universe u

/-- The finite-dimensional extension of the prime field supplies finite generation. -/
instance NumberField.fieldFG (K : Type u) [Field K] [NumberField K] : Field.FG K := by
  have hQ : Field.FG ℚ := by
    refine ⟨⟨∅, ?_⟩⟩
    apply top_unique
    intro q _hq
    simpa only [Rat.cast_id, Finset.coe_empty] using
      (SubfieldClass.ratCast_mem (Subfield.closure (∅ : Set ℚ)) q)
  exact FieldTheory.fg_of_finiteDimensional ℚ K hQ
