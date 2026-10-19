/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationCoefficientSquare
import Nyll.EtaleFundamentalGroups.Inertia.FiniteLevelFieldAlgebra
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Realizing radicals in actual finite normalizations

A root of a power equation over the base ring belongs to an actual finite
normalization inside the prescribed Galois overfield. The ambient inclusion
retains the original root, and the power equation holds in the normalization.
-/

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

universe u v w

/-- An integral radical is realized in a finite normalization of the original overfield. -/
theorem exists_finiteNormalization_radical
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (n : ℕ) (hn : 0 < n) (a : A) (β : L)
    (hpow : β ^ n = algebraMap A L a) :
    ∃ (E : FiniteGaloisIntermediateField K L)
      (b : finiteAbsoluteNormalizationAlgebra A K L E),
      actualFiniteNormalizationAmbientRingHom A K L E b = β ∧
        b ^ n = algebraMap A (finiteAbsoluteNormalizationAlgebra A K L E) a := by
  let E : FiniteGaloisIntermediateField K L :=
    FiniteGaloisIntermediateField.adjoin K {β}
  have hβ : β ∈ E.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin K {β} (Set.mem_singleton β)
  let βE : finiteLevelFieldAlgebra A K L E := ⟨β, hβ⟩
  have hβE : βE ^ n = algebraMap A (finiteLevelFieldAlgebra A K L E) a := by
    apply Subtype.ext
    exact hpow
  have hint : IsIntegral A βE := IsIntegral.of_pow hn (by
    rw [hβE]
    exact isIntegral_algebraMap)
  let b : finiteAbsoluteNormalizationAlgebra A K L E := ⟨βE, hint⟩
  refine ⟨E, b, rfl, ?_⟩
  apply Subtype.ext
  exact hβE

end AnabelianGeometry.WeightFiltration
