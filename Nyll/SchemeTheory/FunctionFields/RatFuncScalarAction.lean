/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic

/-! # The algebra-induced scalar action on rational functions -/

@[expose] public section

/-- Select the action supplied by the chosen algebra on rational functions. -/
abbrev RatFunc.algebraSMul
    {R K : Type*} [CommSemiring R] [Field K] [Algebra R (RatFunc K)] :
    SMul R (RatFunc K) :=
  (inferInstance : Algebra R (RatFunc K)).toSMul
