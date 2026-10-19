/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RootsOfUnityFieldEmbedding

/-!
# Constant coefficients for actual Kummer ratios

If a constant field contains a primitive nth root, every ratio of a root and
its image under an action fixing its nth power is an actual constant nth root.
-/

noncomputable section

namespace AnabelianGeometry.WeightFiltration

/-- A Kummer ratio descends to constants containing all roots of the prescribed exponent. -/
theorem exists_constant_kummerRatio
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    (n : ℕ) (hn : n ≠ 0) (hroot : ∃ ζ : k, IsPrimitiveRoot ζ n)
    (σ : L →+* L) (β : L) (hβ : β ≠ 0) (hfixed : σ (β ^ n) = β ^ n) :
    ∃ δ : rootsOfUnity n k, algebraMap k L (δ.val : k) = σ β / β := by
  let : NeZero n := ⟨hn⟩
  have hsβ : σ β ≠ 0 := by
    intro h
    exact hβ (σ.injective (h.trans (map_zero σ).symm))
  have hr : (σ β / β) ^ n = 1 := by
    rw [div_pow, ← map_pow, hfixed, div_self (pow_ne_zero n hβ)]
  let u : Lˣ := Units.mk0 (σ β / β) (div_ne_zero hsβ hβ)
  let z : rootsOfUnity n L := ⟨u, by
    apply Units.ext
    exact hr⟩
  obtain ⟨δ, hδ⟩ :=
    (RamificationTheory.HilbertRamification.restrictRootsOfUnity_bijective_of_primitiveRoot
      (algebraMap k L) n hroot).2 z
  exact ⟨δ, congrArg (fun r : rootsOfUnity n L => (r.val : L)) hδ⟩

end AnabelianGeometry.WeightFiltration
